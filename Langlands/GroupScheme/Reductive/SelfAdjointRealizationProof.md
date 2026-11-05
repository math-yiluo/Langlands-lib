# Actual adjoint-stable realization of a connected reductive group: proof

Authors: Worker 1359 and Worker 1655.

The theorem
`Langlands.GroupScheme.SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement`
proves exactly the published proposition
`Langlands.GroupScheme.ConnectedReductiveSelfAdjointRealizationStatement.{u}`,
imported from `Langlands.GroupScheme.Reductive.SelfAdjointRealizationStatement`.

For every `RCLike k : Type u` and every actual group scheme `G` over `Spec k`
with `IsConnectedReductive G`, it constructs a natural number `d` and a matrix
representation `ρ : MatrixRepresentation G (Fin d)` such that `ρ` is a closed
immersion (`IsClosedSubgroup ρ`) and the range of
`ρ.affineMatrix (CommAlgCat.of k k)` is stable under conjugate transpose.
The universe `u` is arbitrary. Both the real case (`RCLike.I = 0`) and the
complex case are covered.

## Chosen realization

The module also packages the theorem as data, for use by later modules. For
`k : Type u` with `RCLike k`, a group scheme `G` over `Spec k`, and
`hG : IsConnectedReductive G`:

- `realizationDim k G hG : ℕ` is the matrix size `d` chosen by
  `Classical.choose` from the theorem;
- `realization k G hG : MatrixRepresentation G (Fin (realizationDim k G hG))`
  is the representation `ρ` chosen with it;
- `realization_spec k G hG` states that `realization k G hG` satisfies
  `IsClosedSubgroup`, and that the range of its `affineMatrix` at
  `CommAlgCat.of k k` is stable under `star`.

These are definitions by choice: nothing is claimed about which realization is
chosen beyond `realization_spec`.

## Implemented proof

### Reduction to a positive definite form

The published `affineLinearEmbeddingStatement` (module
`Langlands.GroupScheme.AffineLinearEmbeddingProof`) gives a closed matrix
representation `ρ : MatrixRepresentation G (Fin N)`. It applies because
`IsConnectedReductive G` makes the structure morphism affine and smooth.
The proof then finds `J : GL (Fin N) k` such that:

- `J` is positive definite;
- `J⁻¹ * star g * J` lies in the rational range of `ρ` whenever `g` does.

The published `exists_closed_starStable_of_positiveForm` (module
`Langlands.GroupScheme.MatrixRepresentationPositiveForm`) turns such a form
into a closed representation `σ` whose rational range is stable under
`star`. That `σ` is the representation returned.

### Algebraically closed coefficients

`exists_posDef_form` treats an `RCLike` field `S` that is algebraically closed.
Let `H` be the rational range of a closed representation `ρ` of a connected
reductive `G` over `Spec S`. Then:

1. `H` is polynomially defined (`affineMatrix_range_isPolynomiallyDefined`,
   module `Langlands.GroupScheme.MatrixRepresentationPolynomialImage`).
2. The semisimplicity bridge
   `PolynomialSemisimplicity.isSemisimpleRepresentation_rightTranslation`
   (module `Langlands.GroupScheme.Reductive.PolynomialSemisimplicity`, accepted
   candidate `f017fafd`, not yet in the Library) shows that
   right translation by `H` on polynomial functions is semisimple. Its hypothesis
   `IsPseudoReductive G` comes from `IsConnectedReductive.isPseudoReductive`.
   The resulting representation is, by definition, the representation
   `ClosedOrbit.subgroupRep H`, and Lean accepts it as that instance.
3. The closed-orbit theorem `ClosedOrbit.exists_conj_star_mem` (module
   `Langlands.Group.ClosedOrbit`, Worker 1571's accepted candidate `c5594572`,
   not yet in the Library) gives `x : GL n S` such that
   `x⁻¹ * star g * x ∈ H` whenever `x⁻¹ * g * x ∈ H`.
4. `FormSelfAdjointMean.isFormSelfAdjoint_star_mul_self` turns this into
   self-adjointness of `H` for the form `star x * x`, and
   `posDef_star_mul_self` shows that the form is positive definite.

### Fields with trivial conjugation

`exists_posDef_form_of_real` treats an `RCLike` field `k` on which `star` is
trivial. It uses an algebraically closed `RCLike` field `S` with
`Algebra k S` and `IsScalarTower ℝ k S`.

- **Base change.** The group `G_S` is connected reductive
  (`connectedReductiveFieldExtensionStatement`). The base change of `ρ` is still a
  closed immersion (`isClosedSubgroup_baseChange`, from the published
  `IsClosedSubgroup.baseChange` and the general-linear base-change isomorphism).
- **Range comparison.** `baseChange_affineMatrix_affinePointsBaseChangeMulEquiv`
  shows that, through the published `affinePointsBaseChangeMulEquiv`, the base
  change of `ρ` has the same matrices on `S`-points of `G_S` as `ρ` on
  `S`-valued points of `G`. Its proof uses `pointMatrix_eq_affineMatrix`,
  `pointMatrix_baseChange` and `pointMatrix_naturality`. The restriction-of-scalars
  isomorphism of test spectra has identity underlying morphism. Hence the
  rational range of the base change equals `(ρ.affineMatrix (CommAlgCat.of k S)).range`.
- **Form over `S`.** The algebraically closed case gives a positive definite
  form `J` over `S` for this range.
- **Real form.** The range is polynomially defined. Because conjugation of `S`
  fixes the image of `k`, the range is stable under entrywise conjugation
  `conjGL` (`conjGL_mem_range`). The published
  `FormSelfAdjointMean.exists_real_form` (geometric mean of `J` and its
  conjugate) then gives a positive definite form `m` that is fixed by `conjGL`
  and makes the range self-adjoint.
- **Descent.** A `conjGL`-fixed invertible matrix has real entries.
  `exists_map_eq_of_conjGL_eq` writes it as the image of `m₀ : GL n k`, using
  real parts of entries for both the matrix and its inverse.
  `posDef_of_map` descends positive definiteness of `m` to `m₀`. Membership in
  the range reflects along `k → S` (`map_mem_range_iff`, via the zero-locus
  description and injectivity of `k → S`). `map_star` shows that the entrywise
  map commutes with `star`. Hence `m₀` makes the rational range of `ρ` over `k`
  self-adjoint.

### Transport to arbitrary `RCLike` fields and universes

The main theorem splits on whether `RCLike.I = 0` in `k`.

- **`I ≠ 0`.** Then `RCLike.im I = 1`, so `RCLike.complexRingEquiv` gives a
  ring equivalence `k ≃+* ℂ`. `isAlgClosed_of_ringEquiv` transfers algebraic
  closure across universes, and the algebraically closed case applies to `k`.
- **`I = 0`.** Conjugation on `k` is trivial. Take `S = ULift.{u} ℂ`. Its
  `RCLike` structure `liftRCLike` is transported from `ℂ` with the published
  `Analytic.rclikeOfNormPreservingRingEquiv`. The algebra `liftAlgebra` sends
  `z` to its real part, through `RCLike.realRingEquiv`. `liftAlgebra_scalarTower`
  checks compatibility with `ℝ`. Algebraic closure again comes from
  `isAlgClosed_of_ringEquiv`. These are local `let` instances inside the proof
  only; no global instance is declared.

## Auxiliary declarations

Two public lemmas in `Langlands.GroupScheme.MatrixRepresentation` may be reused:

- `baseChange_affineMatrix_affinePointsBaseChangeMulEquiv`: scalar extension
  of a matrix representation compared on rational points of the base change.
- `isClosedSubgroup_baseChange`: base change preserves `IsClosedSubgroup`.

In `Langlands.GroupScheme.SelfAdjointRealization`, the public theorems are:

- `exists_posDef_form`: the algebraically closed case;
- `exists_posDef_form_of_real`: the trivial-conjugation case.

The main theorem and the chosen-realization declarations `realizationDim`,
`realization` and `realization_spec` (described above) are public too.
Everything else is private.

## Provenance

The helpers `isAlgClosed_of_ringEquiv` and `liftRCLike`, and the shape of
`map_mem_range_iff` and of the `ULift ℂ` case split, are adapted from Worker
1655's staged Levi-Iwasawa modules (candidates `b9f52fdc` and `47761347`). This
is why Worker 1655 is listed as a coauthor.

The overall route is internal. It is a Kempf–Ness/closed-orbit argument
followed by a geometric-mean descent from `ℂ` to `ℝ`. It does not formalize a
specific theorem of the literature. The classical results it corresponds to are:

- G. D. Mostow, *Self-adjoint groups*, Annals of Mathematics (2) 62 (1955),
  44–55, source
  `provided-5f1e15cecfb548442c95672963225326a5c335720f06432665e0053e9be8aec7`,
  Theorems 7.1–7.2: fully reducible complex and real algebraic matrix groups
  have self-adjoint conjugates;
- A. Borel and Harish-Chandra, *Arithmetic Subgroups of Algebraic Groups*,
  Annals of Mathematics (2) 75 (1962), 485–535, source
  `borel-harish-chandra-arithmetic-subgroups-1962`, Lemma 1.8 and Theorem 1.9.

These are the sources cited by the statement module. The proof uses neither
compact real forms nor Lie-algebra Cartan involutions.
