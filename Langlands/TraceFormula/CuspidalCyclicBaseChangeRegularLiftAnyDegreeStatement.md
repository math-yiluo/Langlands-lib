# Cuspidal cyclic lift with the regular σ-lift identity

`Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement.{u, uV, uW}`
states the existence of a cuspidal base change from `GL_{r+1}(𝔸_K)` to
`GL_{r+1}(𝔸_L)` for a cyclic extension `L/K` of any degree. Its hypotheses are
those of `CuspidalCyclicBaseChangeLiftAnyDegreeStatement`, binder for binder and
in the same order. Its conclusion has the six clauses of that proposition, with
clauses 1–4 and 6 verbatim; clause 5 has the same quantification, instance block,
local data and existentials, and asserts the regular σ-lift identity
`IsRegularSigmaLift` in place of the σ-lift `IsSigmaLift`. The module states the
proposition and does not prove it.

## Notation and transport

For a finite place `v` of `K`, write `K_v` for `v.adicCompletion K`. An element
`w : FinitePlacesAbove L v` is a finite place `w.1` of `L` above `v` with the
evidence that it lies above `v`; write `L_w` for `w.1.adicCompletion L`. The
terms `w.1.asIdeal.ramificationIdx (𝓞 K)` and `w.1.asIdeal.inertiaDeg (𝓞 K)` are
its ramification index and residue degree. The module imports
`Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftStatement` for its transports:

- `tensorPlaceAboveHom v w : K_v ⊗[K] L →+* L_w` is the `w`-component of
  `finiteTensorMap v`;
- `tensorPlaceAboveRepresentation v w ρ` pulls back a representation `ρ` of
  `GL_{r+1}(L_w)` to `GL_{r+1}(K_v ⊗[K] L)` along the group map induced by
  `tensorPlaceAboveHom v w`;
- `completionPlaceAboveRepresentation v w ρ` pulls back `ρ` to `GL_{r+1}(K_v)`
  along the group map induced by `FiniteExtension.completionMap v w.1 : K_v →+* L_w`.

It imports `Langlands.BaseChange.SigmaDiscreteRegularDescentStatement` for the
predicate `IsRegularSigmaLift`. No new predicate or transport is defined.

A `CuspidalOperatorRealization K r` realizes an irreducible representation in the
cuspidal form space. A `CuspidalSpectralPresentation` of it is a restricted tensor
presentation of a nonzero finite slice; its `localComponent v` is the embedded local
realization of the factor at `v`, its `spectralSystem.exceptional` is a finite set
of finite places, and `spectralSystem.eigenvalues v hv` is the unordered tuple of
normalized Satake parameters at `v` outside that set. `Eigenvalues.power m` raises
each entry to the power `m`, keeping multiplicities.

## Hypotheses

Number fields `K` and `L` in one universe `u`, with `[Algebra K L]`,
`[CompactSpace (AdeleQuotient K)]` and `[CompactSpace (AdeleQuotient L)]`;
`σ : L ≃ₐ[K] L` and `l : ℕ` with `IsCyclicAlgebra σ l`, so that `L/K` is cyclic of
degree `l` with generator `σ` (any degree, one included);
`IsCyclicShiftSplit K L x.Completion σ l` at every infinite place `x` of `K`;
`r : ℕ`, `S : CuspidalOperatorRealization K r` and
`D : CuspidalSpectralPresentation.{u, uV} S`, with
`ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S` and
`(D.localComponent v).IsIrreducible ∧ (D.localComponent v).IsAdmissible` at every
finite place `v`; two finite places `v₁ ≠ v₂` with
`IsCyclicShiftSplit K L (vᵢ.adicCompletion K) σ l` and
`(D.localComponent vᵢ).IsSupercuspidal` for `i = 1, 2`.

## Conclusion

There exist `T : CuspidalOperatorRealization L r` and
`P : CuspidalSpectralPresentation.{u, uW} T` such that:

1. `ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`.
2. `P.spectralSystem.IsArithmeticWeakBaseChangeOf D.spectralSystem`.
3. For every finite `v` and `hv : v ∉ D.spectralSystem.exceptional` such that every
   `w : FinitePlacesAbove L v` has `w.1.asIdeal.ramificationIdx (𝓞 K) = 1`, there is
   `hw : ∀ w : FinitePlacesAbove L v, w.1 ∉ P.spectralSystem.exceptional` with
   `P.spectralSystem.eigenvalues w.1 (hw w) =
   (D.spectralSystem.eigenvalues v hv).power (w.1.asIdeal.inertiaDeg (𝓞 K))` for every `w`.
4. For every finite `v` with `IsCyclicShiftSplit K L (v.adicCompletion K) σ l` and every
   `w : FinitePlacesAbove L v`, there is a `Representation.Equiv` from
   `completionPlaceAboveRepresentation v w (P.localComponent w.1).representation` to
   `(D.localComponent v).representation` (stated as `Nonempty` of that type).
5. For every finite `v` and `w : FinitePlacesAbove L v` with `∀ w', w' = w`: give
   `E_v = K_v ⊗[K] L` its module topology over `K_v`, with the local field data of
   `CompletionPadic.topologicalData v` on `K_v`; put
   `σv = Algebra.TensorProduct.congr AlgEquiv.refl σ`, `πv = (D.localComponent v).representation`
   and `PiV = tensorPlaceAboveRepresentation v w (P.localComponent w.1).representation`.
   There exist `hπ : Langlands.IsAdmissible πv`, `hP : Langlands.IsAdmissible PiV`,
   `A : SigmaIntertwiner σv (r + 1) PiV` and `c : ℂ` with
   `IsRegularSigmaLift σv l πv hπ PiV hP A c`. That is, `c ≠ 0`, and for all Haar
   measures `μF` on `GL_{r+1}(K_v)` and `μE` on `GL_{r+1}(E_v)` and all
   Schwartz–Bruhat functions `φ` on `GL_{r+1}(E_v)` and `f` on `GL_{r+1}(K_v)` that are
   concordant for these measures, with `φ` supported in the σv-regular set, `f`
   supported in the regular semisimple set and `det g ∈ N_{E_v/K_v}(E_vˣ)` whenever
   `f g ≠ 0`, the twisted trace `tr(PiV(φ) ∘ A)` for `μE` equals `c · tr πv(f)` for `μF`.
6. For every finite place `w` of `L`,
   `(P.localComponent w).IsIrreducible ∧ (P.localComponent w).IsAdmissible`.

At a finite place with `g` places above it and `1 < g < l` (possible only for
composite `l`), only clauses 3 and 6 apply, as in
`CuspidalCyclicBaseChangeLiftAnyDegreeStatement`.

## Difference from `CuspidalCyclicBaseChangeLiftAnyDegreeStatement`

The two propositions differ only in the last line of clause 5:
`IsRegularSigmaLift σv l πv hπ PiV hP A c` here, `IsSigmaLift σv l πv hπ PiV hP A c`
there. `IsSigmaLift` requires `c ≠ 0` and the trace identity for all concordant
pairs; `IsRegularSigmaLift` requires `c ≠ 0` and the identity only for the pairs
described in clause 5. So `CuspidalCyclicBaseChangeLiftAnyDegreeStatement` implies the
present proposition, with the same `T`, `P`, `hπ`, `hP`, `A` and `c`.

In the other direction, `RegularSigmaLiftUpgradeStatement` (module
`Langlands.BaseChange.RegularSigmaLiftUpgradeStatement`) states that, under its eight
premises, an `IsRegularSigmaLift` between irreducible admissible representations over
a cyclic algebra is an `IsSigmaLift` with the same intertwiner and constant. At a place
`v` with one place `w` above it, `tensorPlaceAboveHom v w` is bijective because
`finiteTensorMap v` is (`completedTensorComparison`), so the irreducibility of `PiV`
follows from clause 6, and `cyclicAlgebraBaseChange` gives `IsCyclicAlgebra σv l`.
Hence the present proposition, together with `RegularSigmaLiftUpgradeStatement` and
its premises, gives `CuspidalCyclicBaseChangeLiftAnyDegreeStatement`. The present
proposition isolates the global trace comparison from that local passage.

## Why the statement holds

For `r ≥ 1`, compare the simple trace formula for `GL_{r+1}` over `K` with its
twisted form over `L`. Put a supercuspidal matrix coefficient at `v₁` and a
strongly regular elliptic test of nonzero trace at `v₂`, with split transfers at
both places, cyclic convolution at the other split places (the infinite ones
included), spherical transfer at the unramified places outside the exceptional
set, and concordant tests with σ-regular and regular support elsewhere, as in
Henniart–Lemaire II.6.13. At a place `v` with one place above it, take a
concordant pair with σ-regular and regular support and with the determinants of the
ordinary support in the norm group. Separating the spectra by the spherical Hecke
algebras gives the analogue of Arthur–Clozel (6.2),
`l · tr(Π(φ) I_σ) = ∑_{π'} tr π'(f)`, where `Π` is the σ-stable cuspidal lift, `I_σ`
the operator by which `σ` acts on its space of cusp forms, `l` the degree of `L/K`, and `π'` runs over the lower
cuspidal representations whose Satake parameters have the same residue-degree
powers as those of the given representation `π`. By the fibre theorem
(Arthur–Clozel III.3.1) these are the twists `π ⊗ (χ ∘ det)` by idele class
characters `χ` trivial on the idele norms from `L`; these characters form a cyclic
group of order `l`. The local component `χ_x` of such `χ` at a place `x` of `K` is
trivial on the local norms, and at every place the ordinary test has the same trace
against `π_x` and `π_x ⊗ (χ_x ∘ det)`: at `v` because `χ_v ∘ det` is `1` on the
support of the test (the determinant condition of clause 5); at split places because
every determinant is a norm, so `χ_x = 1`; at unramified places because the
spherical transfer is supported in the kernel of `χ_x ∘ det`; and at the remaining
places because the regular orbital integrals of an ordinary test matching a twisted
one vanish off norms, so Weyl integration gives equal traces (Henniart–Lemaire
II.6.13; Arthur–Clozel, printed p. 57: "on the image of the norm, their local
characters coincide"). So all the twists have the same trace. If they form `m`
distinct isomorphism classes, `m` divides `l` and the sum is `m · tr π(f)`, so
`tr(Π(φ) I_σ) = (m / l) · tr π(f)`. In Arthur–Clozel the Steinberg component at the
auxiliary inert place excludes nontrivial self-twists, so `m = l` and (6.2) becomes
(6.3), `tr(Π(φ) I_σ) = tr π(f)`, with coefficient one. The present setting has no
such place, and the nonzero factor `m / l` is absorbed into the constant `c` of
clause 5, which `IsRegularSigmaLift` only requires to be nonzero.
Factorizing the traces and fixing nonzero local factors away from `v` gives the
local identity at `v` with a nonzero constant. Clauses 1–4 and 6 arise as for
`CuspidalCyclicBaseChangeLiftAnyDegreeStatement`, whose Markdown describes the
construction of `P` and the case `r = 0`.

## Sources and derivation

The proposition is derived content: it isolates the global part of the trace
comparison behind `CuspidalCyclicBaseChangeLiftAnyDegreeStatement`, before the local
passage from regularly supported pairs to all concordant pairs.

- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula*, Annals of Mathematics Studies 120 (1989), source
  `arthur-clozel-1989-base-change`, retained PDF SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`. Chapter 1, §6.3,
  printed pp. 54–56: Theorem III.3.1 quoted on p. 54; the comparison (6.2) on p. 55,
  which equates `ℓ` times the twisted trace of the lift (`ℓ` the cyclic degree) with
  the sum over the cuspidal fibre; the argument on p. 55 that the Steinberg component
  at the inert place makes the fibre consist of `ℓ` distinct twists; and (6.3) on
  p. 56, which uses that their traces agree on functions in the image of base change.
  On printed p. 57, "on the image of the norm, their local characters coincide."
  Chapter III, Theorem 3.1, printed p. 201, is the fibre theorem for arbitrary cyclic
  degree. [Arthur–Clozel, §6.3](https://www.math.toronto.edu/arthur/pdf/30.pdf#page=68)
- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour
  `GL_n` en caractéristique non nulle*, Mém. SMF 124 (2011), source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, retained
  PDF SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  §II.6.1, printed p. 118, sets up the global comparison for a cyclic extension of
  global function fields of any degree, with the distinguished place inert (the
  characteristic-zero case is referred there to Arthur–Clozel, Ch. 1, §6.3). §II.6.13,
  printed pp. 129–130, obtains from it a nonzero constant and the trace identity at
  the distinguished place for concordant pairs with σ-regular and regular support,
  using Weyl integration for the twists. §II.2.7, printed p. 67, defines the σ-lift
  with the constant on the ordinary side, as in `IsSigmaLift` and
  `IsRegularSigmaLift`; §II.6.13 writes its identity with the constant on the twisted
  side, which is the same assertion with the inverse constant.
  [Henniart–Lemaire, §II.6](https://www.numdam.org/item/10.24033/msmf.436.pdf#page=126)

Arthur–Clozel §6.3 globalizes a discrete series with a Steinberg component at an
auxiliary inert place (Lemma 6.5); the present formulation instead takes a supplied
spectral presentation with two split supercuspidal places. The identity of clause 5
is asserted only on the pairs of `IsRegularSigmaLift`. These form a subset of the
pairs of Henniart–Lemaire II.6.13, which impose no determinant condition at the
distinguished place.
