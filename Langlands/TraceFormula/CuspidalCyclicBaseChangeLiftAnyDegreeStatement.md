# Cuspidal base change for cyclic extensions of arbitrary degree

`Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftAnyDegreeStatement.{u, uV, uW}`
states the existence of a cuspidal base change from `GL_{r+1}(𝔸_K)` to
`GL_{r+1}(𝔸_L)`. Applying the proposition to the arguments of
`CuspidalCyclicBaseChangeLiftStatement` other than `l.Prime` gives the prime-degree
proposition. Both have the same six conclusions.

## Notation and transport

For a finite place `v` of `K`, write `K_v` for `v.adicCompletion K`. An element
`w : FinitePlacesAbove L v` consists of a finite place `w.1` of `L` above `v`
and the evidence that it lies above `v`. Write `L_w` for `w.1.adicCompletion L`.
The terms `w.1.asIdeal.ramificationIdx (𝓞 K)` and
`w.1.asIdeal.inertiaDeg (𝓞 K)` are its ramification index and residue degree.

The following transports come from `CuspidalCyclicBaseChangeLiftStatement`.

- `tensorPlaceAboveHom v w : K_v ⊗[K] L →+* L_w` is the `w`-component of
  `finiteTensorMap v`. The finite-place part of `completedTensorComparison`
  identifies `K_v ⊗[K] L` with the product of the `L_w`, so this component is
  an isomorphism when there is a single place above `v`.
- `tensorPlaceAboveRepresentation v w ρ` pulls back `ρ` from `GL_{r+1}(L_w)`
  along the group map induced by `tensorPlaceAboveHom v w`.
- `completionPlaceAboveRepresentation v w ρ` pulls back `ρ` along the group map
  induced by `FiniteExtension.completionMap v w.1 : K_v →+* L_w`.

A `CuspidalOperatorRealization K r` realizes an irreducible representation in
the cuspidal form space. A `CuspidalSpectralPresentation` gives a restricted
tensor presentation of a nonzero finite slice of that realization. Its
`localComponent v` is the embedded local realization of the factor at `v`.
Its `spectralSystem.exceptional` is a finite set of finite places, and
`spectralSystem.eigenvalues v hv` is the unordered tuple of normalized Satake
parameters at `v` outside that set. The operation `Eigenvalues.power` raises
each entry to the specified power, keeping its multiplicity.

## Hypotheses

Take number fields `K` and `L` in the same universe `u` with `[Algebra K L]`
and the compactness instances `[CompactSpace (AdeleQuotient K)]` and
`[CompactSpace (AdeleQuotient L)]` for the additive adele quotients. Take
`σ : L ≃ₐ[K] L` and `l : ℕ` with `IsCyclicAlgebra σ l`. In this field
setting, `L/K` is cyclic of degree `l` with generator `σ`, and degree one
is allowed. At every infinite place `x` of `K` assume
`IsCyclicShiftSplit K L x.Completion σ l`. This predicate identifies the
tensor algebra over the completion with `l` copies of the completion, with
`id ⊗ σ` acting by cyclic shift.

Let `r : ℕ`, `S : CuspidalOperatorRealization K r`, and
`D : CuspidalSpectralPresentation.{u, uV} S`. Assume
`ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S`,
so a continuous unitary idele class character acts centrally on `S`.
Assume `(D.localComponent v).IsIrreducible ∧ (D.localComponent v).IsAdmissible`
at every finite place `v`. Require two distinct finite places `v₁` and `v₂` with
`IsCyclicShiftSplit K L (vᵢ.adicCompletion K) σ l` and
`(D.localComponent vᵢ).IsSupercuspidal` for each `i`.

## Conclusion

There exist `T : CuspidalOperatorRealization L r` and
`P : CuspidalSpectralPresentation.{u, uW} T` with the following properties.

1. `T` has unitary central character.
2. `P.spectralSystem.IsArithmeticWeakBaseChangeOf D.spectralSystem` holds. On
   a cofinite set of base places both spectra are defined, every place above
   is unramified, and the upper parameters are the lower ones raised to the
   residue degree.
3. For every finite `v`, given `hv : v ∉ D.spectralSystem.exceptional` and
   ramification index one at every place `w` above `v`, there is
   `hw : ∀ w : FinitePlacesAbove L v, w.1 ∉ P.spectralSystem.exceptional`.
   For every such `w`, the equality is
   `P.spectralSystem.eigenvalues w.1 (hw w) =
   (D.spectralSystem.eigenvalues v hv).power (w.1.asIdeal.inertiaDeg (𝓞 K))`.
4. At each finite `v` with `IsCyclicShiftSplit K L (v.adicCompletion K) σ l`
   and every `w` above it, there is a `Representation.Equiv` from
   `completionPlaceAboveRepresentation v w (P.localComponent w.1).representation`
   to `(D.localComponent v).representation`, expressed as `Nonempty` of that type.
5. For every finite `v` and `w : FinitePlacesAbove L v` with `∀ w', w' = w`,
   give `E_v = K_v ⊗[K] L` its module topology over `K_v`, using the local field
   data of `CompletionPadic.topologicalData v` on `K_v`. Put
   `σv = Algebra.TensorProduct.congr AlgEquiv.refl σ`. Write `πv` for
   `(D.localComponent v).representation` and `PiV` for
   `tensorPlaceAboveRepresentation v w (P.localComponent w.1).representation`.
   There exist `hπ : Langlands.IsAdmissible πv`, `hP : Langlands.IsAdmissible PiV`,
   `A : SigmaIntertwiner σv (r + 1) PiV` and `c : ℂ` with
   `IsSigmaLift σv l πv hπ PiV hP A c`. Here `A` intertwines `PiV` with its
   twist by `σv`. The lift requires `c ≠ 0` and
   `tr(PiV(φ) ∘ A) = c · tr(πv(f))` for all choices of Haar measures and
   concordant Schwartz–Bruhat pairs `(φ, f)` for those measures.
6. For every finite place `w` of `L`,
   `(P.localComponent w).IsIrreducible ∧ (P.localComponent w).IsAdmissible`.

For prime `l`, clauses 4 and 5 together cover all finite places. For composite
`l`, there may be `g` places above `v` with `1 < g < l`. The algebra `E_v`
then has `g` field factors permuted transitively by `σ`. The local conclusions
there are clause 3 under its unramifiedness and exceptional-set conditions
and clause 6 in all cases. In particular, there is no lift relation using
`σ^g` on any one factor. Henniart–Lemaire §II.6.20 formulates a σ-lift for
the representation over the entire cyclic algebra `E_v`.

## Trace comparison

For `r ≥ 1`, use a supercuspidal matrix coefficient at `v₁` and a strongly
regular elliptic test of nonzero trace at `v₂`. Choose split transfers at
both places so that the upper tests impose the corresponding support and
cuspidality conditions in the simple twisted formula. Use cyclic convolution
at the other split places, including the infinite ones. Away from the
auxiliary places, use spherical transfer at the unramified places where the
lower spectrum is defined and concordant tests elsewhere. At intermediate
places, this matching is for the cyclic algebra `E_v`. In particular,
matching near the identity allows a lower test of nonzero trace by averaging
over a sufficiently small compact open subgroup fixing a nonzero vector.

Compare the two simple trace formulas in the unitary central character
sectors, using the norm pullback of the lower central character upstairs.
Separate the spectra by varying the matching spherical Hecke factors.
Arthur–Clozel III.3.1 identifies the remaining lower classes by equality of
residue-degree powers as determinant twists by characters trivial on the
idele norm. These twists have equal traces on matching tests. The reason is
that regular orbital integrals vanish off norms and the twisting characters
are trivial on the determinants of norms. The selected sum is nonzero when
the local trace factors for the given representation are nonzero. Strong
multiplicity one then singles out the σ-stable cuspidal lift with the
transferred spectrum. This argument uses the fibre description for arbitrary
cyclic degree and does not require the twists to be pairwise distinct.

Fixing the nonzero trace factors away from a place and varying the tests at
that place gives the local comparisons. At a split place the twisted tensor
trace is the trace against cyclic convolution, and character independence
identifies the factors with the lower component. At the auxiliary places,
the split tests can put the supercuspidal coefficient in turn on the factor
being identified. At a place with one place above it, factorization gives a
nonzero scalar and a twisted trace identity on concordant tests supported on
the lower determinant-norm subgroup. For a general concordant pair, the
ordinary test can be restricted to that subgroup without changing any
regular orbital integral. Weyl integration and the locally integrable
character therefore preserve its trace. This gives the identity for all
concordant pairs required by `IsSigmaLift`.

At each place in clause 3, spherical transfer gives an upper spherical
component with the residue-degree power of the lower parameters. Use
irreducible admissible factors and choose spherical reference vectors at
all those places when forming `P`. This keeps the corresponding upper
places out of the exceptional set and gives clauses 2, 3 and 6. For `r = 0`,
pull back the unitary idele class character by the norm. The local norm
identities give the split and one-place clauses, and the norm of an upper
uniformizer has lower valuation equal to the residue degree. In degree one,
transport along the field isomorphism gives the identity base change.

## Sources and derivation

- Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
  the Trace Formula* (1989), source `arthur-clozel-1989-base-change`, retained
  PDF SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  Chapter 1, §6.3, printed pp. 54–57, gives a trace comparison in arbitrary
  cyclic degree for the globalization of Lemma 6.5, which includes a
  Steinberg component at an inert place. Equations (6.2)–(6.4) give the
  lifting comparison and its Whittaker normalization. Chapter III,
  Theorem 3.1, printed p. 201, supplies the fibre theorem for arbitrary
  cyclic degree used in the comparison. The present formulation adapts
  that comparison to a supplied spectral presentation with two split
  supercuspidal components. [Arthur–Clozel, §6.3](https://www.math.toronto.edu/arthur/pdf/30.pdf#page=68)

- Henniart and Lemaire, *Changement de base et induction automorphe pour GLₙ
  en caractéristique non nulle* (2011), source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
  retained PDF SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  §II.2.7, printed p. 67, gives the σ-lift condition with a nonzero scalar.
  §II.6.1, printed p. 118, sets up the global comparison over a function
  field with arbitrary degree. §II.6.13, printed pp. 129–130, uses Weyl
  integration and local trace factorization. §§II.6.18–II.6.19, printed
  pp. 132–134, use globalized lifts to compare generators and to prove pair
  factor identities. §II.6.20, printed p. 135, describes the strong partial
  global lifting. The Library proposition adapts the existence and local
  comparisons to number fields with split infinite places and the specified
  spectral presentations. [Henniart–Lemaire, §II.6](https://www.numdam.org/item/10.24033/msmf.436.pdf#page=126)

- Flath, *Decomposition of representations into tensor products* (1979),
  source `flath-1979-tensor-products`, retained *Corvallis*, Part I PDF
  SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
  Theorems 2–3, printed p. 181, supply the irreducible admissible factors and
  the restricted tensor product with chosen reference vectors.
