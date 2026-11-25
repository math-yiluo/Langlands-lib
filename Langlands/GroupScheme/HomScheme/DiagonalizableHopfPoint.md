# Homomorphisms from diagonalizable groups as Hopf points

Module `Langlands.GroupScheme.HomScheme.DiagonalizableHopfPoint`, namespace
`Langlands.GroupScheme.HomScheme.DiagonalizablePoint`.

The module turns group-scheme homomorphisms from a diagonalizable group `D(Λ)` to an affine
group scheme `G` over `Spec R`, after base change to `Spec C`, into Hopf points
`O(G) → C ⊗[R] R[Λ]`. It also reads naturality, closed immersions and equality of ranges on
these Hopf points. Here `Λ` is an arbitrary commutative group in `Type u`: neither finite
generation nor torsion-freeness is assumed. It generalizes the split-torus section
`SplitTorusPoint` of `HomScheme.SplitTorusHopfPoint` (the case `Λ = ℤ^I`) and the
two-source kernel criteria of `HomScheme.SplitTorusRangeKernel`. It is infrastructure for the
chart construction in the proof of `MultiplicativeTypeEtaleLiftStatement` (multiplicative-type
subgroups of a fibre lift to an étale neighbourhood). There the charts parametrize closed subgroups of
multiplicative type through Hopf points with values in `C ⊗[R] R[(ℤ^r) × F]`, with `F` a
finite abelian group.

Notation, all from the Library:

- `RelativeMultiplicativeType.diagonalizable S Λ` is the diagonalizable group `D_S(Λ)` over
  `S` (`Torus.RelativeMultiplicativeType`).
- `RelativeHom H G T` is a homomorphism `H_T ⟶ G_T` over `T`, and `evaluate a j` is its base
  change along `a : T' ⟶ T` (`HomScheme.Universal`).
- `specOver R C` is `Spec C` as a scheme over `Spec R`, and `specMap g` is `Spec` of an
  `R`-algebra map `g : C → D` (`HomScheme.AffineTest`).
- `AffineCoordinates.hopfAlgebra G` is the coordinate Hopf algebra `O(G)`.
- `IsHopfPoint R f` says that `f : O(G) →ₐ[R] C ⊗[R] P` is a Hopf point, that is, compatible
  with comultiplication, counit and antipode. `pushPoint R g f` is `f` followed by
  `g ⊗ id` (`Langlands.Algebra.FiniteBialgebraHom`).
- `AlgHom.liftEquiv R C _ _ f : C ⊗[R] O(G) →ₐ[C] C ⊗[R] P` is the `C`-linear extension of `f`.
- `IsClosedSubgroup j` says that the underlying scheme map of `j` is a closed immersion.
- `TorusSubgroupModuli.evaluate j a` is the family of subgroups cut out by `j` after base
  change along `a`, and `SubgroupFunctor.range` is the range of a homomorphism as a subgroup
  functor.

## Definitions

- `diagonalizableHopfIso R Λ : hopfGroup R (AddMonoidAlgebra R Λ) ≅ diagonalizable (Spec R) Λ`.
  It composes two Library isomorphisms. `Diagonalizable.hopfSpecIso` identifies the Hopf
  spectrum of the group algebra `R[Λ]` with the diagonalizable group scheme `D(Λ)` of
  `Torus.DiagonalizableHopf`. `Diagonalizable.relativeModelIso` (from
  `Torus.AffineRelativeDiagonalizable`) identifies the latter with the relative model
  `RelativeMultiplicativeType.diagonalizable (Spec R) Λ`.
- `diagPointEquiv G C`, for `G` over `Spec R` with `IsAffine G.X.left` and an `R`-algebra `C`,
  is an equivalence between
  `RelativeHom (diagonalizable (Spec R) Λ) G (specOver R C)` and the subtype of Hopf points
  `O(G) →ₐ[R] C ⊗[R] R[Λ]`. It is the inverse of `transportEquiv` along
  `(diagonalizableHopfIso R Λ).symm` and `coordinateIso G` (from
  `HomScheme.FiniteDiagonalizableHom`), followed by `FiniteSource.pointEquiv`. As in the
  split-torus case, `pointEquiv` is defined for arbitrary Hopf algebras, so `R[Λ]` need not be
  finite over `R`.

## Results

Here `f` and `f'` are Hopf points `O(G) → C ⊗[R] R[Λ]` and `O(G) → C ⊗[R] R[Λ']`, and
`g : C →ₐ[R] D`.

- `diagPointEquiv_symm_apply f`: the homomorphism of `f` is the `transport` of the Hopf-spectrum
  homomorphism `(pointEquiv _ _ C).symm f`. This holds by definition.
- `evaluate_diagPointEquiv_symm g f` (naturality): base change along `specMap g` sends the
  homomorphism of `f` to the homomorphism of `pushPoint R g f`. The proof uses the Library
  lemmas `evaluate_transport` and `evaluate_specMap`. `diagPointEquiv_evaluate g j` states
  the same on Hopf points: the Hopf point of `evaluate (specMap g) j` is `pushPoint R g` of the
  Hopf point of `j`.
- `isClosedSubgroup_diagPointEquiv_symm_iff f`: the homomorphism of `f` is a closed subgroup
  exactly when the `C`-linear extension `C ⊗[R] O(G) → C ⊗[R] R[Λ]` of `f` is surjective. This
  combines the Library lemmas `isClosedSubgroup_transport_iff` and
  `FiniteSource.isClosedSubgroup_pointEquiv_symm_iff`.
- `evaluate_diagPointEquiv_symm_eq_range g f`: the family `TorusSubgroupModuli.evaluate` of
  the homomorphism of `f` along `specMap g` is the range of the homomorphism of
  `pushPoint R g f`. The proof applies the Library lemma `evaluate_eq_range` and then
  naturality.
- `range_diagPointEquiv_symm_le_iff_ker₂ f f' hf`: if the extension `φ` of `f` is surjective,
  then the range of the homomorphism of `f'` lies in the range of the homomorphism of `f`
  exactly when `ker φ ≤ ker φ'`, where `φ'` is the extension of `f'`. The two sources `D(Λ)`
  and `D(Λ')` may differ. The proof transports the Library two-source criteria
  `range_transport_le_iff₂` and `range_pointEquiv_symm_le_iff_ker₂` of
  `HomScheme.SplitTorusRangeKernel`.
- `range_diagPointEquiv_symm_eq_iff_ker₂ f f' hf hf'`: if both extensions are surjective, the
  two ranges are equal exactly when the two kernels are equal. This applies the previous
  lemma in both directions. `range_diagPointEquiv_symm_eq_iff_ker` is the special case
  `Λ' = Λ`.

## Provenance

The module is internal infrastructure; it formalizes no single cited result. Its content is
the standard description of homomorphisms from a diagonalizable group to an affine group
scheme through coordinate rings. A homomorphism `D(Λ)_C → G_C` is a map of Hopf algebras
`C ⊗ O(G) → C[Λ]`, the character group being the group-like elements of `C[Λ]`. It is a
closed immersion exactly when this map is surjective. Two closed subgroups given this way
are equal exactly when the kernels agree. The proofs repeat those of the split-torus
section of `HomScheme.SplitTorusHopfPoint` with `ℤ^I` replaced by `Λ`.
