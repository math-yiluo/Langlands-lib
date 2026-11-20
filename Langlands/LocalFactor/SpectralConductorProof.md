# Tate's spectral conductor formula for supplied local-constant systems: proof

Worker 96 wrote this module for Task 5626 (24b84ed8-5c32-460b-b50b-30a1c08fb408). It
assembles three theorems that are already in the Library. Worker 4803 wrote the
reduction and its supporting modules. Worker 96, with Worker 4803 and Worker 4918, wrote
the rank-one conductor proof. The refinement theorem is in module
`Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof`. The same three-term
composition already appears inline in two Library proofs:
`Langlands.Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`
(module `Langlands.Correspondence.HenniartSupercuspidalConductorReductionProof`) and
`Langlands.Correspondence.ArithmeticPairEpsilonExistence.conditionalDeligneValue_monomial`
(module `Langlands.Correspondence.ArithmeticPairEpsilonExistenceProof`). Neither of them
states it as a separate theorem. This module does.

## Result

`Langlands.LocalFactor.ConductorExponent.spectralConductor` has type

```
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
  Langlands.LocalFactor.ConductorExponent.SpectralConductorStatement.{uF, uV} F
```

The universe levels `uF` (the field) and `uV` (the representation carrier) are
independent parameters of the theorem. The target proposition is defined in module
`Langlands.LocalFactor.ConductorExponentStatement`. It says the following. Fix a
reciprocity family `e`, an assignment `ε` with `NonabelianSystem.IsSystem F e ε`, a
nontrivial continuous unitary additive character `ψ` of the bottom field `base F` (type
`CommonClosure.AdditiveCharacter F (base F)`, which is
`HarmonicAnalysis.UnitaryAdditiveCharacter` and has a field `nontrivial : ψ ≠ 1`), an
additive Haar measure `μ` of `base F`, a genuine
continuous representation `A` of `W_F = weilSubgroup F (base F)`, a finite-inertia
presentation `P` of `A` on the local Weil group, and surjectivity `hsurj` of
`weilInertiaRestriction F P.extension`. Then for every `s ∈ ℂ`

```
ε(A ⊗ ω_s, ψ, μ) = ε(A, ψ, μ) · q_F^(-(a(A) + n(ψ) · dim A) · s),
```

with `a(A) = P.artinConductor hsurj`, `n(ψ) = additiveConductor F ψ` (Tate's `n(ψ)`, the
largest `n` with `ψ(π^(-n) O) = 1`) and
`q_F = baseCardinality F`. In Lean the two sides are
`conditionalDeligneValue F e ε hε (base F) ψ μ (baseClass F A hA) s` and the same value at
`s = 0` times the complex power of `q_F`.

The theorem adds no hypothesis to the target. In particular it assumes no conductor,
reciprocity, ramification, induction-formula or local-constant proposition. The only
axioms are `propext`, `Classical.choice` and `Quot.sound`; `lean_check` inspection of the
declaration reports exactly these and the level parameters `uF`, `uV`.

## Implemented proof

After introducing `p`, the instance `Fact p.Prime` and `F`, the proof is the single term

```
SpectralConductor.spectralConductorRankOneReduction.{uF, uV} F
  (fun A => Ramification.Padic.finiteInertiaConductorRefinement F A)
  (SpectralConductor.commonClosureRankOneConductor p F)
```

1. `spectralConductorRankOneReduction.{uF, uV}` proves
   `SpectralConductorRankOneReductionStatement.{uF, uV}`. Applied to `F`, it reduces
   `SpectralConductorStatement.{uF, uV} F` to two premises.
2. The first premise asks for
   `FiniteInertiaConductorRefinementStatement.{uF, max uF uV} F A` for every
   `A : FiniteRepresentation.{0, uF, max uF uV} ℂ (localWeilGroup F)`. The theorem
   `finiteInertiaConductorRefinement F A` supplies it. That theorem holds at arbitrary
   independent universes `uF` and `uV'`. Here Lean instantiates its carrier universe
   `uV'` as `max uF uV`.
3. The second premise is `CommonClosureRankOneConductorStatement F`. The theorem
   `commonClosureRankOneConductor p F` supplies it.

## Imported results

### The reduction

`Langlands.LocalFactor.SpectralConductor.spectralConductorRankOneReduction` (module
`Langlands.LocalFactor.SpectralConductorReduction`) proves
`SpectralConductorRankOneReductionStatement.{uF, uV}`. That proposition says: for every
prime `p` and every `F : PadicField.{uF} p`, if every finite-dimensional complex
representation of the local Weil group with carrier universe `max uF uV` satisfies
`FiniteInertiaConductorRefinementStatement`, and
`CommonClosureRankOneConductorStatement F` holds, then
`ConductorExponent.SpectralConductorStatement.{uF, uV} F` holds. Its proof is Tate's
argument "via inductivity in degree 0". Let `x` be the class of `A`.

- Degree-zero generation. The Library's `commonClosureDegreeZeroGeneration` (module
  `Langlands.LocalFactor.CommonClosureGenerationProof`), made finite by
  `exists_finset_generators`, writes `x - dim A · 1` as an integral combination of
  finitely many induced differences `Ind_L(χ - χ')` of continuous characters of
  intermediate Weil groups `W_L`.
- A common finite level. `exists_presentingField` (module
  `Langlands.LocalFactor.SpectralConductorChoice`) chooses an actual finite Galois
  subfield `M ⊇ P.extension` that contains every inducing field `L` and at which every
  `χ, χ'` is presented: `IsPresentedAt F M L χ` (module
  `Langlands.LocalFactor.SpectralConductorInduction`) says that `χ` is trivial on the
  elements of `W_L` that lie in Weil inertia and act trivially on `M`. Equivalently, the
  restriction of `χ` to the inertia elements of `W_L` factors through their restriction to
  `M`, which is a finite group. This does not require `χ` to be trivial on all of inertia,
  so ramified generators are allowed. Triviality on the whole inertia subgroup of `W_L`
  would make `χ` and `χ'` unramified, and both rank-one conductors in the difference
  would be zero.
- A conductor functional. `conductorFunctional F M` (module
  `Langlands.LocalFactor.SpectralConductorFunctional`) is an additive map on the virtual
  classes of the base. It is Serre's class-function form
  `|I|^(-1) Σ_γ m(γ) (f(1) - f(γ))` of the Artin conductor on the inertia group `I` of
  `M/F`. Times `log q_F`, it vanishes on the trivial class (`conductorFunctional_one`).
  On a generator it equals `(a(χ̃) - a(χ̃')) log q_L`, where `χ̃` is the field character
  attached to `χ` by the component of `e` at `L`. This value comes from the degree-zero
  case of Serre's induction formula (`conductorFunctional_induce_eq`, module
  `Langlands.LocalFactor.SpectralConductorInduction`) and from the residue-degree
  identity `inductionFactor_mul_logCardinality` (module
  `Langlands.LocalFactor.SpectralConductorDegree`). It also uses
  `lClassSum_eq_characterConductor` (module
  `Langlands.LocalFactor.SpectralConductorRankOneBridge`). That lemma is where the
  rank-one premise and the normalization `hε.1 : NormalizedReciprocity F e` enter.
- The epsilon side. In module `Langlands.LocalFactor.SpectralConductorEpsilon`, the
  classes `y` with `ε(ω_s y) = ε(y) · exp(-s (a(y) + n(ψ) deg y log q_F))` form an
  additive subgroup (`formulaSubgroup`). The generators lie in it
  (`induce_mem_formulaSubgroup`). This uses the system's induction relation and the
  rank-one spectral formula at `L`, where the additive conductor of `ψ ∘ Tr_(L/F)`
  cancels. The trivial class lies in it (`one_mem_formulaSubgroup`). Hence so does `x`
  (`mem_formulaSubgroup_of_span`).
- Identification of the conductor. `conductorFunctional_baseClass` shows that the
  functional at `x` is the Artin expression of the refined presentation
  `P.refine M hPM`. The first premise, applied to `P`, `M`, `hsurj` and the
  surjectivity of `weilInertiaRestriction F M`
  (`Ramification.HerbrandBridge.weilInertiaRestriction_surjective`), identifies this with
  `P.artinConductor hsurj`. Finally `deg x = dim A`,
  `log q_F = Complex.log (baseCardinality F)` (`residueCardinality_base`), and
  `Complex.cpow_def_of_ne_zero` turn the exponential into the complex power of the
  target.

### Refinement invariance of presentation conductors

`Langlands.Ramification.Padic.finiteInertiaConductorRefinement` (module
`Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof`) has type

```
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)),
  FiniteInertiaConductorRefinementStatement F A
```

`FiniteInertiaConductorRefinementStatement F A` (module
`Langlands.LocalFactor.Ramification.InertiaPresentationStatement`) says the following.
Let `P` be a finite-inertia presentation of `A`, let `M ⊇ P.extension` be a finite
Galois subfield with inclusion `h`, and let `hP` and `hM` be the surjectivity proofs. Then
`(P.refine M h).artinConductor hM = P.artinConductor hP`, and likewise for the Swan
conductor. The theorem applies `presentation_conductors_eq` to `P.refine M h` and `P`.
That lemma compares any two presentations `P`, `Q` of the same `A`. For a presentation,
let `c(v)` be the codimension of the fixed space of the upper ramification group `G^v`
of its finite extension, acting through its inertia representation. The proof uses two
formulas.

- Swan conductor (`inertiaSwanConductor_eq_integral`): it equals `∫_0^B c(v) dv` for
  every `B ≥ φ(b)`. Here `φ` is Herbrand's function and `b` is a lower index from which
  the lower ramification groups are trivial (`ramificationCutoff`).
- Artin conductor (`inertiaArtinConductor_eq_integral`): it equals
  `c(0) + ∫_0^B c(v) dv`. The term `c(0)` is the tame part, the codimension of the fixed
  space of the whole inertia group.

`HerbrandBridge.presentationUpperFixedComparison` identifies, at every index `v ≥ 0`
including `v = 0`, the fixed space of each presentation with one space defined from the
absolute upper groups of the Weil group. So the two presentations have the same profile
`c` on `[0, ∞)`. Take `B` as the larger of their two bounds. Then the integrals agree,
which gives the Swan equality. The Artin equality also needs the equality of `c(0)`,
and the proof uses it separately. This term matters: a ramified tame line has Swan
integral zero but codimension one at index zero. There is no continuity hypothesis on
`A`.

### Rank-one conductor transport

`Langlands.LocalFactor.SpectralConductor.commonClosureRankOneConductor` (module
`Langlands.LocalFactor.SpectralConductorRankOneProof`) has type

```
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p), CommonClosureRankOneConductorStatement F
```

`CommonClosureRankOneConductorStatement F` (module
`Langlands.LocalFactor.SpectralConductorRankOneStatement`) says the following. Let `e`
satisfy `NormalizedReciprocity F e`, let `L` be an intermediate field, let `M ⊇ L` be an
actual finite Galois subfield, and let `χ` be a continuous character of `W_L`. Let `ρ` be
a character of the inertia group of `M/L` that agrees with `χ` on Weil inertia. Then the
Artin expression `inertiaArtinConductor` of `ρ` equals the multiplicative conductor of
the field character `fieldCharacterEquiv F e L χ`. The proof identifies, for every real
`s ≥ 0`, the bound `a(χ̃) ≤ ⌈s⌉₊` with triviality of `ρ` on the upper group `G^s(M/L)`.
It uses upper-numbering local class field theory
(`LocalClassField.absoluteUpperReciprocityTheorems`) and Herbrand's theorem in absolute
form. It then reads the Artin expression off this upper-numbering profile
(`Ramification.Padic.inertiaArtinConductor_rankOne_eq_of_upper_levels`).

## Sources

- `tate-1979-number-theoretic-background`: J. Tate, *Number theoretic background*,
  Corvallis Part II (1979), (3.4.5), printed p. 15 (PDF p. 24):
  `ε(V ω_s, ψ, dx) = ε(V, ψ, dx) f(V)^(-s) δ(ψ)^(-s dim V)` with `δ(ψ) = q_F^(n(ψ))` and
  `f(V) = q^(a(V))`. On the same page Tate derives (3.4.2)–(3.4.8) from the rank-one case
  "via inductivity in degree 0 and (2.3.1)". He also characterizes `f` as the unique
  function inductive in degree 0 with `f(χ) = q^(a(χ))` for quasi-characters. The
  imported reduction follows this route.
- `deligne-1973-local-constants`: P. Deligne, *Les constantes des équations
  fonctionnelles des fonctions L*, LNM 349 (1973), (5.5.2), printed p. 548 (PDF p. 48):
  `ε(V, ψ, dx, s) = ε(V, ψ, dx) q^(-(a(V) + dim V · n(ψ)) s)`.
- `serre-1979-local-fields`: J.-P. Serre, *Local Fields* (1979). VI §2, Propositions 2
  and 4, printed pp. 100–102 (PDF pp. 107–109), give the class-function form of the Artin
  conductor and the conductor of an induced representation. XV §2, printed pp. 227–228
  (PDF pp. 232–233), gives upper-numbering reciprocity. The imported theorems use these.
