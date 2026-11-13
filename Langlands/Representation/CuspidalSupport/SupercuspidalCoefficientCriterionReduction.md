# Renard VI.2.1, (a) ⇔ (b): the reverse implication and a reduction to the joint statement

Author: Worker 157. Module
`Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This module proves two things:

- the implication (b) ⇒ (a) of Renard VI.2.1, with no structural premise;
- a **conditional reduction** of the full published equivalence
  `SupercuspidalCoefficientCriterionStatement` to the one published, still unproved
  statement `JointSpecialCompactBasisExistenceStatement`.

It does **not** prove `SupercuspidalCoefficientCriterionStatement` unconditionally.
Only the direction (a) ⇒ (b) depends on the premise.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026. It is registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The relevant
passage is VI.2.1, Théorème and proof, printed pp.137–139 / PDF pp.143–145. The theorem
states that, for a smooth representation `(π, V)` of `G`, the following are equivalent:
(a) `(π, V)` is supercuspidal, (b) its matrix coefficients have compact support modulo
the centre `Z(G)`, (c) its restriction to `⁰G` is compact.

## Statement

```lean
def SupercuspidalCoefficientCriterionReductionStatement : Prop :=
  JointSpecialCompactBasisExistenceStatement.{u} →
    SupercuspidalCoefficientCriterionStatement.{u, v}
```

`supercuspidalCoefficientCriterionReduction` proves it. The premise and the conclusion are
published statements, used unchanged.

- `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisStatement`; Renard V.5.1–V.5.2).
  Take any nonarchimedean local field `F : Type u`, connected reductive `G`, maximal split
  torus `i` and generic cocharacter `ν`. Then there are one apartment datum `D`, one
  special point `x`, a closed subgroup scheme `j : Z ⟶ G` representing the torus
  centralizer, and a character comparison. At these, `K0 = D.specialCompactSubgroup x`
  has the special compact properties, the Iwasawa and Cartan comparisons and the
  simultaneous basis property. Task 4169 (`8c39faa0-2a70-4fc4-a027-914987aba924`) owns
  its proof.
- `SupercuspidalCoefficientCriterionStatement.{u, v}` (module
  `Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionStatement`;
  Renard VI.2.1 (a) ⇔ (b)). Let `A : SmoothRep.{0, u, v} ℂ G(F)` be a representation of
  a connected reductive group over a nonarchimedean local field `k : Type u`. Then
  `IsSupercuspidal A` holds if and only if, for every `w ∈ A` and every smooth vector `ℓ`
  of the dual action, `Function.support (matrixCoefficient A.representation ℓ w) ⊆ C · Z`
  for some compact `C`. Here `Z = Subgroup.center G(F)`.

The reduction keeps the conclusion's universes `u` (field) and `v` (carrier). It adds no
other hypothesis.

## Declarations

| Declaration | Content |
| --- | --- |
| `exists_isCompact_superset_mul_center_inter` | general topological-group lemma (below) |
| `compactNormKernelRestriction_of_coefficients_compactModCenter` | (b) ⇒ (c), unconditional |
| `isSupercuspidal_of_coefficients_compactModCenter` | (b) ⇒ (a), unconditional |
| `coefficients_compactModCenter_of_isSupercuspidal` | (a) ⇒ (b), from the joint statement |
| `SupercuspidalCoefficientCriterionReductionStatement` | the reduction statement (a `Prop`) |
| `supercuspidalCoefficientCriterionReduction` | its proof |

## The proof

### A group lemma: `exists_isCompact_superset_mul_center_inter`

Let `Γ` be a topological group and `H` an open subgroup such that `H ∩ Z(Γ)` is compact.
Then for every compact `C` there is a compact `K` with `(C · Z(Γ)) ∩ H ⊆ K`.

- The open sets `H c = {x | x c⁻¹ ∈ H}`, for `c ∈ C`, cover `C`. Take a finite subcover
  indexed by a finite set `t`.
- For each `c`, let `z_c` be a central element with `c z_c ∈ H`, chosen with `Classical.choose`
  when one exists. Otherwise set `z_c = 1`.
- Take `K = C · {z_c : c ∈ t} · (H ∩ Z(Γ))`. It is compact because it is a product of a
  compact set, a finite set and a compact set.
- Let `x = c z ∈ H` with `c ∈ C` and `z` central. Pick `c' ∈ t` with `c c'⁻¹ ∈ H`. Then
  `c' z = (c c'⁻¹)⁻¹ (c z) ∈ H`, so `z_{c'}` exists and `c' z_{c'} ∈ H`. Hence
  `z_{c'}⁻¹ z ∈ H ∩ Z(Γ)`, and `x = c · z_{c'} · (z_{c'}⁻¹ z) ∈ K`.

### (b) ⇒ (c): `compactNormKernelRestriction_of_coefficients_compactModCenter`

Condition (c) is the published `HasCompactNormKernelRestriction A`. It says that every
coefficient of the restriction of `A` to `⁰G = Plancherel.rationalCommonNormKernel G`,
taken against a smooth vector of the restricted dual, has compact support in `⁰G`.

- A smooth dual vector for the restriction to `⁰G` is a smooth dual vector for `G(F)`
  (`Plancherel.isSmoothVector_dual_rationalNormKernel_iff`, which uses that `⁰G` is open).
  Hypothesis (b) therefore gives a compact `C` with support in `C · Z`.
- The group lemma applies to `H = ⁰G`. Its hypotheses are
  `Plancherel.isOpen_rationalCommonNormKernel` and
  `Plancherel.isCompact_rationalCommonNormKernel_inf_center` (Renard V.2.6: `⁰G ∩ Z` is
  compact). It gives a compact `K ⊇ (C · Z) ∩ ⁰G`.
- `⁰G` is closed (`Plancherel.isClosed_rationalCommonNormKernel`), so its inclusion is a
  closed embedding. The preimage of `K` in `⁰G` is therefore compact. It contains the
  support of the restricted coefficient, so that coefficient has compact support
  (`HasCompactSupport.of_support_subset_isCompact`).

### (b) ⇒ (a): `isSupercuspidal_of_coefficients_compactModCenter`

Compose (b) ⇒ (c) with the published (c) ⇒ (a), `isSupercuspidal_of_compactRestriction`
(module `Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal`).
Its four structural premises are all published theorems: `parabolicDynamic`,
`smoothMaximalSplitTorusConjugacy`, `standardCocharacter` and `relativeRootSystem`. No
premise remains.

### (a) ⇒ (b): `coefficients_compactModCenter_of_isSupercuspidal`

Premise: `JointSpecialCompactBasisExistenceStatement.{u}`. Let `A` be supercuspidal, `w ∈ A`
and `ℓ` a smooth dual vector.

1. Choose a maximal split torus `i : T ⟶ G` and a generic cocharacter `ν`
   (`exists_maximalSplitTorus_genericCocharacter`). The joint statement gives `D`, `x`,
   the centralizer data `(Z, j, s)` and their properties. Write `K0` for
   `D.specialCompactSubgroup x`. It is compact (special compact properties).
2. `rationalPositiveCartanCover` turns the Cartan comparison into a finite Cartan cover. There is a finite set
   `F₀` of torus-centralizer points such that every `g` equals `k₁ f a k₂` with
   `k₁, k₂ ∈ K0`, `f ∈ F₀` and `a ∈ C_A^+`.
3. `isCuspidal_of_all_represented_parabolics_of_standardCocharacter` turns represented
   supercuspidality into cuspidality for the actual standard family.
   `exists_rational_compact_translate_pairing_bound`, applied to the compact set `K0`, then
   gives a bound `B`: if `y` is dominant, `k₁, k₂ ∈ K0`, `f ∈ F₀` and the coefficient is
   nonzero at `k₁ ϖ^y f k₂`, then `⟨β, y⟩ ≤ B` for every simple relative root `β`. The
   Library's (a) ⇒ (c) uses the same bound. Its proof packages the Jacquet-module
   computation of Renard, printed p.139.
4. `cartanDetectionModulo_center` says that the simple-root pairings determine the class
   of `ϖ^y` modulo the centre of `G(F)`. By `CartanDetectionModulo.finite_bounded_image`,
   the classes modulo `Z` of the `ϖ^y` with `0 ≤ ⟨β, y⟩ ≤ B` for all `β` form a finite set.
   Choose one representative of each class (`Function.surjInv` of the quotient map). This
   gives a finite set `T0`.
5. Take `C = K0 · F₀ · T0 · K0`. It is compact because it is a product of compact and
   finite sets. Let `g` be a point where the coefficient does not vanish. Write
   `g = k₁ f ϖ^y k₂` by the cover (`exists_cocharacter_of_mem_CAplus` writes `a = ϖ^y` with
   `y` dominant). Then `g = k₁ ϖ^y f k₂`, because `f` centralizes the torus points
   (`centralizerPoints_le_pointCentralizer`). By step 3, `y` lies in the box `[0, B]`. So
   `ϖ^y = t z` with `t ∈ T0` and `z` central. Since `z` commutes with `k₂`, we get
   `g = (k₁ f t k₂) z ∈ C · Z`.

### The reduction: `supercuspidalCoefficientCriterionReduction`

Introduce the premise and the binders of the target statement. The two directions are the
two theorems above.

## Relation to Renard's proof

Renard proves the theorem as the cycle (b) ⇒ (c) ⇒ (a) ⇒ (b) (printed pp.138–139 / PDF
pp.144–145). The Lean module proves (b) ⇒ (c) and (a) ⇒ (b) and takes (c) ⇒ (a) from the
Library.

- **(b) ⇒ (c)** (printed p.138). Renard works in the quotients. The image of the support in
  `G / Z(G)` is compact. `⁰G / (⁰G ∩ Z(G))` is a closed subgroup of `G / Z(G)`, so it meets
  that image in a compact set. He then lifts this to `⁰G`. Take a compact open subgroup of
  `⁰G / (⁰G ∩ Z(G))`. Its preimage `K` in `⁰G` is compact open, because `⁰G ∩ Z(G)` is
  compact (V.2.6) and an extension of a compact group by a compact group is compact.
  Finitely many translates of `K` then cover the support in `⁰G`. The Lean proof uses the
  same key fact, that `⁰G ∩ Z` is compact. It does not pass to quotient groups. The group
  lemma `exists_isCompact_superset_mul_center_inter` works directly in `G(F)`: a finite
  cover of `C` by open cosets of `⁰G`, one chosen central element per coset, and the compact
  set `⁰G ∩ Z`. This lemma is a general argument written for this module. The finite index
  of `⁰G Z` is not used.
- **(c) ⇒ (a)** (printed p.138) is the published Library implication
  `isSupercuspidal_of_compactRestriction`.
- **(a) ⇒ (b)** (printed pp.138–139). Renard argues by contraposition, using the Cartan
  decomposition `G = K₀ F_∅ C⁺_∅ K₀` (V.5.1). Suppose a coefficient's support is not compact
  modulo the centre. Then some `f ∈ F_∅` and a sequence `t_n ∈ C⁺_∅` meet the support, and
  the `t_n` lie in no subset that is compact modulo the centre. So some simple root `α`
  satisfies `|α(t_n)| → 0` (VI.2.1.1). For the maximal standard parabolic `P_α`, he takes a
  normal open subgroup `K ⊆ K₀` with an Iwahori decomposition that fixes `v` and `λ`. A
  finite-relation computation then gives `π(e_{t_n⁻¹ K_N t_n}) v₁ ≠ 0` for infinitely many
  `n`. Since the subgroups `t_n⁻¹ K_N t_n` exhaust `N`, `v₁ ∉ V(N)`, so `V_N ≠ 0`.

  The Lean proof uses the same ingredients, but it argues directly instead of by
  contraposition, and it uses the finite Cartan cover in place of sequences.
  - The published `exists_rational_compact_translate_pairing_bound` gives a uniform integer
    bound `B`. If the coefficient is nonzero at `k₁ ϖ^y f k₂`, then every simple-root pairing
    of `y` is at most `B`. Its Library proof packages Renard's finite-relation and root-gap
    computation on printed p.139, made uniform over translates in the compact set `K₀`.
    This bound plays the role of the contradiction with (VI.2.1.1).
  - In Renard, unbounded root coordinates follow from "not compact modulo the centre". The
    Lean proof uses the contrapositive: bounded simple-root coordinates leave only finitely many
    classes modulo the centre (`cartanDetectionModulo_center`,
    `CartanDetectionModulo.finite_bounded_image`). These finitely many classes give the
    compact set `C`.

  The published `supercuspidalUnitaryCoefficientCompactSupportStructuralReduction` (module
  `Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportReduction`)
  uses the same Cartan-bound ingredients.
- **A possible alternative, not used.** One could also try to derive (a) ⇒ (b) from the
  Library's (a) ⇒ (c) and the finiteness of `G / ⁰G Z`. This is not Renard's argument. The
  Library's condition (c) controls coefficients only one at a time. For a representation
  that is not admissible, this route would need a uniformity argument in the central
  translate, which the Library does not provide. The module does not take this route.

## What remains

The one premise is `JointSpecialCompactBasisExistenceStatement.{u}`. When it is proved, the
task target is `supercuspidalCoefficientCriterionReduction <proof>`.

## Imports

| Module | Used for |
| --- | --- |
| `…CuspidalSupport.SupercuspidalCoefficientCriterionStatement` | the target statement |
| `…Exponents.RepresentedCompactRestrictionSupercuspidal` | `HasCompactNormKernelRestriction`, `isSupercuspidal_of_compactRestriction`, the joint statement |
| `…Aubert.General.RationalCuspidalCoefficientCompactSupport` | Cartan cover, pairing bound, detection modulo the centre |
| `…Plancherel.RationalNormKernelCentralCover` | `⁰G ∩ Z` compact |
| `…Plancherel.RationalNormKernelSmoothDual` | smooth dual vectors on `⁰G` |
| `…GroupScheme.Absolute.ParabolicDynamicProof`, `…Rational.SmoothMaximalSplitTorusConjugacyProof`, `…Rational.StandardCocharacterProof`, `…Rational.RelativeRootSystemProof` | the four proved structural statements |
