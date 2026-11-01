# Smooth mirabolic induction Φ̂⁺

Author: Worker 749.

This module constructs the Bernstein–Zelevinsky functor
`Φ̂⁺ : Alg P_(n+1) → Alg P_(n+2)` on the actual published smooth complex
representations. It is the smooth (not compactly supported) analogue of the
published normalized `Φ⁺` of
`Langlands.Representation.Derivative.MirabolicPlusNormalization`. Like that
functor, it first twists the input by `|det|^(1/2)`. It then extends the
twisted input to the plus subgroup `Q = P_(n+1) V_(n+2)` by the published
character `thetaPlus`, and applies the Library's actual smooth induction
`Induction.smoothInductionFunctor Q`. That induction acts by right
translation and has no support condition. The module proves:

- the equality with normalization by the actual radical Haar half
  character;
- the evaluation interface: values, covariance, one open subgroup of right
  stabilizers, and construction from a covariant function;
- the action, functoriality and preservation of injective maps and
  monomorphisms;
- the natural inclusion `Φ⁺ ⟶ Φ̂⁺` of the compactly supported functions.

It constructs no adjunction. The adjunction `Φ⁻ ⊣ Φ̂⁺` is in the companion
module `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`.
The module also states no exactness, no composite identity of BZ77
§3.2(d,e,f), no unit or counit, and no submodule-lattice, detection,
derivative or irreducibility statement, and assumes none of them as data.

Its direct imports are
`Langlands.Representation.Derivative.MirabolicPlusNormalization`,
`Langlands.Representation.Induction.Equivalences` (for `smoothFunctionOf`),
`Langlands.Representation.Category.Abelian` (for
`SmoothRep.mono_iff_injective`) and
`Langlands.Representation.Geometric.CompactSmoothComparison` (for
`Induction.compactSmoothInclusion`). No existing Library file is changed.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
source `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
PDF page is the printed page minus 439.

- §1.8(a), printed p.444/PDF5: let `M`, `U` be closed subgroups of `G`
  with `M` normalizing `U`, `M ∩ U = {e}` and `P = MU` closed, and let
  `θ` be a character of `U` normalized by `M`. For a smooth representation
  `(ρ, L)` of `M`, the space `I(L)` consists of the functions `f : G → L`
  with `f(umg) = θ(u) mod_U^(1/2)(m) ρ(m)(f(g))` for `u ∈ U`, `m ∈ M`,
  `g ∈ G`, for which there is an open subgroup of `G` fixing `f` under
  right translation. `G` acts on `I(L)` by right translation; this
  representation is `I_(U,θ)(ρ)`. The compactly induced `i_(U,θ)(ρ)` is
  the subrepresentation of the functions compactly supported modulo `P`.
- §3.1, printed p.450/PDF11: `P_n` is the mirabolic subgroup of
  `G_n = GL(n, F)`, `V = V_n` is its unipotent radical, `G_(n-1)`
  normalizes `V`, `θ(v) = ψ(v_(n-1,n))` for a nontrivial additive character
  `ψ`, and `P_(n-1)` normalizes `θ`.
- §3.2, printed pp.450–451/PDF11–12: the source defines
  `Φ⁺ = i_(V,θ)` and `Φ̂⁺ = I_(V,θ) : Alg P_(n-1) → Alg P_n` (with
  `M = P_(n-1)`, `U = V`), and notes that these functors differ from those
  of its reference [1] (Bernstein–Zelevinsky 1976) by twisting with the
  character `mod^(1/2)`.

The adjunction §3.2(c) is proved in the companion module. Exactness
§3.2(a), the identities §3.2(d,e,f) and Remark 3.3 are not used or stated
here. No errata entry for this source is registered in the literature
index, and the Library has no errata note for it.

### Correspondence

Fix the source's `θ` and the positive exponent. For `Φ̂⁺`, the source's
`M = P_(n-1)` and `MU = P_(n-1) V_n` is the published `plusSubgroup`
`Q`. Unfolding §1.8(a), a vector of `Φ̂⁺(τ)` is a function with

`f(u m x) = θ(u) mod_V(m)^(1/2) τ(m) f(x)`,

one open subgroup of right stabilizers, and no support condition; the group
acts by right translation. The published proved radical Haar comparison
`phiPlusHaarHalf_eq` gives `mod_V(m)^(1/2) = |det m|^(1/2)`. Hence
`Φ̂⁺(τ)` is the smooth induction from `Q` of the representation
`q ↦ thetaPlus(q) • |det(plusProjection q)|^(1/2) • τ(plusProjection q)`,
which is how this module defines it. The published `thetaPlus` restricts to
`θ` on the radical and is trivial on the successor copy of `P_(n+1)`, and
`plusProjection` is the projection `Q → P_(n+1)`.

The Library's smooth induction `Induction.SmoothFunctions Q σ` is the
submodule of smooth vectors, for right translation, of Mathlib's
coinduced module of functions `f` with `f(q x) = σ(q) f(x)`. Its smooth
vectors are exactly the functions with one open subgroup `K` satisfying
`f(x k) = f(x)` for all `x` and `k ∈ K`, the source's condition. The source's
compactly induced subspace is the published compact induction used by `Φ⁺`.
The published comparison `Induction.compactSmoothInclusion` includes it in
the smooth induction, and `phiPlusToPhiHatPlus` below is this inclusion.

### Rank shift

`GeneralLinear.mirabolic n F.Carrier` is the source's `P_(n+1)` and
`GeneralLinear.Mirabolic.radical (n + 1) F.Carrier` is the source's
`V_(n+2)`. Hence `phiHatPlus T ψ n` is the source's
`Φ̂⁺ : Alg P_(n+1) → Alg P_(n+2)` (source index `n + 2`), and
`plusSubgroup n F.Carrier` is the source's `P_(n+1) V_(n+2)`. This is the
indexing of the published `phiPlus T ψ n`. Every `n : ℕ` is allowed,
including `n = 0` (from the trivial group `P_1` to `P_2`), with no case
split.

## Parameters, topology and universes

Throughout, `p : ℕ` is prime (`[Fact p.Prime]`), `F : PadicField.{uF} p`,
and `T : F.TopologicalData` is an arbitrary supplied topological
realization. Every topological statement installs `letI := T.topology`;
statements about the induced function spaces also install
`letI := T.generalLinearTopologicalGroup (n + 1 + 1)`, exactly as the
published plus modules do. No canonical topology is substituted. The
additive character is
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`.
The proofs here do not use its nontriviality.

The coefficient universe of `SmoothRep` is `0` (complex coefficients), the
group universe is `uF`, and the input carrier universe `uV` is an
independent universe parameter. The main types, as declared and checked
(level parameters reported by the Lean inspection: `uV, uF`), are:

```lean
phiHatPlusUnnormalized.{uV, uF} : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  (T : F.TopologicalData) → UnitaryAdditiveCharacter F.Carrier → (n : ℕ) →
  SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
    SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier)
phiHatPlus.{uV, uF} : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  (T : F.TopologicalData) → UnitaryAdditiveCharacter F.Carrier → (n : ℕ) →
  SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
    SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier)
phiPlusToPhiHatPlus.{uV, uF} : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  (T : F.TopologicalData) → (ψ : UnitaryAdditiveCharacter F.Carrier) → (n : ℕ) →
  phiPlus.{uV} T ψ n ⟶ phiHatPlus.{uV} T ψ n
```

The output carrier universe `max uF uV` is the universe of the actual
function space `Induction.SmoothFunctions`, the same as that of the
published `phiPlus`. It is not resized or identified with `uV`.

All main declarations depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Unnormalized Φ̂⁺

`phiHatPlusUnnormalized T ψ n` is the composite

```lean
plusTwistFunctor T ψ n ⋙ SmoothRep.toRep ⋙
  Induction.smoothInductionFunctor (plusSubgroup n F.Carrier)
```

of the published restriction-and-twist functor to `Q` (whose objects carry
`plusTwistRepresentation ψ n τ.representation`, that is,
`q ↦ thetaPlus(q) • τ(plusProjection q)`), the forgetful functor, and the
published smooth induction. Its laws, for every
`τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)`:

- `phiHatPlusUnnormalized_obj_carrier` and `phiHatPlusUnnormalized_obj`:
  the carrier is `Induction.SmoothFunctions (plusSubgroup n F.Carrier) τ'`
  and the object is `SmoothRep.of (Induction.smoothInduced Q τ') _`, with
  `τ' = plusTwistRepresentation ψ n τ.representation` (`rfl`);
- `phiHatPlusEval T ψ n τ φ x : τ`, an `abbrev`, is the value at
  `x : mirabolic (n + 1) F.Carrier`, the published `Induction.eval`;
- `phiHatPlusEval_injective`: vectors are determined by their values;
  `phiHatPlusEval_add`, `phiHatPlusEval_smul`: evaluation is linear;
- `phiHatPlusEval_covariant`: for `q ∈ Q`,
  `φ(q x) = thetaPlus(q) • τ(plusProjection q)(φ x)`;
- `phiHatPlusEval_successor_mul_radical`: in Levi-first coordinates,
  `φ(successor g * u * x) = Θ(u) • τ(g)(φ x)` for `g ∈ P_(n+1)` and
  `u ∈ radical (n + 1)`, where `Θ = theta ψ n` is the published radical
  character;
- `phiHatPlusEval_radical_mul`: `φ(u x) = Θ(u) • φ(x)`;
  `phiHatPlusEval_successor_mul`: `φ(successor g * x) = τ(g)(φ x)`;
- `phiHatPlusEval_exists_openSubgroup`: one open subgroup `K` of
  `mirabolic (n + 1)` with `φ(x k) = φ(x)` for all `k ∈ K` and all `x`;
- `phiHatPlusMk T ψ n τ f hcov K hK` builds a vector from a function with
  the covariance `hcov` and one open subgroup `K` of right stabilizers,
  using the published `Induction.smoothFunctionOf`; no support condition is
  required. `phiHatPlusEval_mk` says its values are `f` (`rfl`);
- `phiHatPlusUnnormalized_action`: right translation,
  `(g • φ)(x) = φ(x g)` (`rfl`); `phiHatPlusUnnormalized_isSmooth`;
- `phiHatPlusUnnormalized_map_hom`: the image of `f : τ ⟶ σ` is the
  published `Induction.smoothInducedMap Q` of the underlying intertwiner of
  `(plusTwistFunctor T ψ n).map f` (`rfl`);
  `phiHatPlusUnnormalized_map_eval`: on values the image is postcomposition,
  `(Φ̂⁺ f)(φ)(x) = f(φ x)` (`rfl`);
- `phiHatPlusUnnormalized_map_injective`: the image of an injective
  intertwiner is injective, by evaluation.

## Normalized Φ̂⁺

`phiHatPlus T ψ n` is defined as

```lean
SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
  phiHatPlusUnnormalized T ψ n
```

where `phiPlusCharacter T n` is the published restriction of
`|det|^(1/2)` (rank `n + 1`) to `P_(n+1)`. This is the normalization of the
published `phiPlus`. `phiHatPlus_eq` states this whole-functor equality
(`rfl`). `phiHatPlus_haarNormalization` states that `phiHatPlus T ψ n`
equals the same composite with the actual Haar half character
`phiPlusHaarHalf T n` and its open-kernel witness
`isOpen_ker_phiPlusHaarHalf T n`. The proof rewrites by the published proved
comparison `phiPlusHaarHalf_eq`. These are equalities of functors, so they
include maps.

Its laws, for every `τ`:

- `phiHatPlus_obj_carrier` and `phiHatPlus_obj`: the carrier is
  `Induction.SmoothFunctions Q τ''` and the object is
  `SmoothRep.of (Induction.smoothInduced Q τ'') _`, with
  `τ'' = plusTwistRepresentation ψ n (Langlands.twist (phiPlusCharacter T n) τ.representation)`
  (`rfl`);
- `phiHatPlusNormalizedEval T ψ n τ φ x : τ`, an `abbrev`, is
  `phiHatPlusEval` for the twisted input, whose carrier is that of `τ`;
- `phiHatPlusNormalizedEval_injective`;
- `phiHatPlusNormalizedEval_covariant`: for `q ∈ Q`,
  `φ(q x) = thetaPlus(q) • |det(plusProjection q)|^(1/2) • τ(plusProjection q)(φ x)`,
  the source covariance with `mod_V^(1/2) = |det|^(1/2)`;
- `phiHatPlusNormalizedEval_radical_mul`: `φ(u x) = Θ(u) • φ(x)`;
- `phiHatPlusNormalizedEval_successor_mul`:
  `φ(successor g * x) = |det g|^(1/2) • τ(g)(φ x)`;
- `phiHatPlusNormalizedEval_exists_openSubgroup`;
- `phiHatPlusNormalizedMk` builds a vector from a function with the
  normalized covariance and one open subgroup of right stabilizers;
  `phiHatPlusNormalizedEval_mk` says its values are the function (`rfl`);
- `phiHatPlus_action`: right translation (`rfl`);
- `phiHatPlus_map_eval`: `(Φ̂⁺ f)(φ)(x) = f(φ x)` (`rfl`);
- `phiHatPlus_map_injective`: the image of an injective intertwiner is
  injective; `phiHatPlus_map_mono`: `Φ̂⁺` preserves monomorphisms, through
  the published `SmoothRep.mono_iff_injective`.

## The compact Φ⁺ inside Φ̂⁺

`phiPlusToPhiHatPlus T ψ n : phiPlus T ψ n ⟶ phiHatPlus T ψ n` is the
natural inclusion of the compactly supported functions. It is the whiskering

```lean
Functor.whiskerLeft
  (SmoothRep.twistFunctor (phiPlusCharacter T n) _ ⋙ plusTwistFunctor T ψ n ⋙ SmoothRep.toRep)
  (Induction.compactSmoothInclusion (plusSubgroup n F.Carrier))
```

of the published natural inclusion of compact into smooth induction. So
naturality is inherited, not reproved. `phiPlusToPhiHatPlus_eval` says that
it keeps every value: the image of `φ` has the values
`phiPlusNormalizedEval T ψ n τ φ x` (`rfl`). `phiPlusToPhiHatPlus_injective`
says that each component is injective.

## Provenance

`Φ̂⁺` is the source's definition `I_(V,θ)` of §1.8(a) and §3.2. The
correspondence above derives the implementation from §1.8(a) and the
published radical Haar comparison: a `|det|^(1/2)` twist followed by the
Library's smooth induction. The evaluation laws, functoriality, injectivity
and the inclusion are internal derivations from the cited Library
constructions and Mathlib. The module asserts no original-literature
theorem.

## Import and dependency audit

The recursive `Langlands` import closure of this module consists of 83
modules: this module and 82 published, paired modules of the Library at
base `b22e185743f7c318f709e14e422801f4360105d5`. They are the `GL`,
mirabolic, mirabolic-projection, radical and radical-Haar group modules;
the harmonic-analysis modules (additive characters and p-adic Haar
scaling); local-field, topology and nonarchimedean-subgroup modules; and the
smooth, smooth-part, transfer, twist, real-power, matrix-coefficient, dual,
admissibility, filtration, Whittaker, Jacquet
coinvariant/localization/positive-character/smooth-twist, induction
(`Definitions`, `Equivalences`, `Parabolic`, `CompactQuotientProof`,
`StructuralStatement`), geometric (`ClosedSubgroupDefinitions`,
`SmoothSupportFiltration`, `CompactSmoothComparison`) and category
(`Basic`, `Twist`, `Abelian`) representation modules. The only derivative
modules are `MirabolicCharacter`, `MirabolicMinus`,
`MirabolicMinusNormalization`, `MirabolicPlus` and
`MirabolicPlusNormalization`, all actual constructions and character
adapters.

The closure contains no classification, segment, multisegment, socle, head,
Jacquet-formula, square-integrability, tempered, exhaustion, product
irreducibility, detection, highest-derivative, pairing, mixed-product or
homogeneity module. Hence neither this module nor any import depends on the
tasks of the complete inherited exclusion set recorded in the context of
task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4` revision 2 (including
`23189526…`, `f3a69bc8…`, `aca8805b…`, `23e98d90…`, `2ae5cbe5…`,
`8364e73f…`, `3bfb61fa…`, `ebea9a8a…`, `20e4e1c6…`, `52e97845…`,
`1cb45da2…`, `cd8ab97c…`, `bf433f0a…`, `30341ae4…`, `8252833d…` and
`5eece9e8…`), their conclusions or consequences. It does not use the
operator-paused minus-exactness task `b65bc667…`, and it uses no
Zelevinsky 1980 result and no BZ77 theorem of §3.2–§3.8. Only the §1.8 and
§3.2 definitions are implemented. No exactness, adjunction or
classification theorem is assumed, and no theorem-valued premise is added.
The proofs use no `sorry`, `admit` or new axiom. This closure inventory is
an author audit, not independent acceptance evidence.
