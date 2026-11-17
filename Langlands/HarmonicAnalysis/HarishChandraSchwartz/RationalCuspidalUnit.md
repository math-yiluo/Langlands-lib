# The cuspidal unit `°e` of Proposition VIII.4.1 (rank adapter, abstract layer)

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, literature ID `waldspurger-2003-plancherel`.
Relevant passages: the proof of Proposition VIII.4.1, printed pp. 328–329
(PDF pp. 94–95), which uses Remark VIII.2.2 and Lemma VIII.2.3.

This module is unit 3 ("rank adapter") of Task 7439, revision 2. Its provenance is
**derived**. The source proves the properties of `°e` in a few lines. This module
packages them as an interface for the kernel step (unit 2) and derives them from
named laws of an operator.

## What the source does

Let `H` be a compact open subgroup of `G` and `e = 1_H` its characteristic function.
The source text says "Notons e la fonction caractéristique de H": `e` is **not**
normalized by `mes(H)⁻¹`. Applying the degree-zero projection `f ↦ °f` of VIII.2
gives `°e`. The source lists these properties (p. 328):

* `°e ∈ °C_H`, by the "relation évidente"
  `°(ρ(g₁)λ(g₂)f) = ρ(g₁)λ(g₂)°f` for all `f ∈ C(G)` and `g₁, g₂ ∈ G`;
* `°e` is real-valued: `\overline{°e} = °(ē) = °e`, by Remark VIII.2.2;
* `°e` is supported in `G¹`: `χ °e = °(χ e) = °e` for `χ ∈ Im X(G)`, by the same
  remark.

The proof then uses (p. 329) `ϕ ∗ °e = ϕ ∗ e = mes(H) ϕ` for `ϕ ∈ °C_H`, by
Lemma VIII.2.3. The source also uses the claim `α(·, g₂) ∈ °C_H` for
`α(g₁, g₂) = mes(H)⁻² ∫_H °e(g₁⁻¹ h g₂) dh`. Because this function of `g₁` involves
`°e(g₁⁻¹ ·)`, the module also records the symmetry `°e(x⁻¹) = °e(x)`. It follows
from the check identity `(°f)ˇ = °(fˇ)` of Remark VIII.2.2, since `eˇ = e`.

## What this module states and proves

**Status.** The actual degree-zero projection of Task 7277 is not in the Library.
This module therefore does **not** state or prove anything about that operator.
Instead it works with an arbitrary complex-linear operator
`P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ`.
It names each law that the source uses as a separate proposition and proves that
these laws imply the interface predicate for `P(1_H)`. Every law stays a hypothesis.
None is assumed or proved for any particular operator.

### Generic facts (proved)

* `convolution_indicator_of_rightInvariant`: let `mu` be a left-invariant measure on
  a group `Γ`, `H` a measurable subgroup, and `φ` a function with `φ(x h) = φ(x)` for
  all `h ∈ H`. Then the Library's `convolution mu φ 1_H x`, that is
  `∫ φ(h) 1_H(h⁻¹ x) dmu(h)`, equals `mu.real H * φ x`. This is the source's last
  equality `ϕ ∗ e = mes(H) ϕ`.
* `comap_subtype_univ_toReal`: for a measurable subgroup `H`,
  `((mu.comap (↑) : Measure H) univ).toReal = mu.real H`. With
  `μH := μG.comap (↑)`, the constant `(μH Set.univ).toReal` in the Library's
  `kernelAlphaChi` and `finiteDimensional_of_kernelAlphaChi` (`KernelQuotient`)
  is therefore `mes(H)`.

### Unitary unramified characters (proved)

* `rationalUnitaryUnramifiedCharacters G` is an abbreviation for the Library's
  `unitaryUnramifiedCharacters`, applied to the actual rational norm characters
  `rationalNormCharacters G`. It consists of the continuous characters
  `G(F) → ℂˣ` that lie in the Library's unramified characters for these norm
  characters and are unitary. This is Waldspurger's `Im X(G)`, as the Library's
  docstring states.
* `rationalUnitaryUnramified_eq_one_of_mem`: these characters are trivial on
  `G¹ = rationalCommonNormKernel G`.
* `exists_unitaryUnramified_ne_one`: if `x ∉ G¹`, some `χ` in
  `rationalUnitaryUnramifiedCharacters G` has `χ(x) ≠ 1`. The proof uses
  `mem_rationalCommonNormKernel_iff_valuation` to find a rational character `c` whose
  valuation `n = ord(c(x))` is nonzero. It takes `χ(g) = u^{ord(c(g))}` with
  `u = exp(π i / n)`, built from the Library's continuous order character
  `rationalOrderContinuousCharacter G c`. Then `χ` is unitary, trivial on `G¹`, and
  `χ(x) = exp(π i) = -1`.

### The interface predicate (definition, entry declaration)

`IsRationalCuspidalUnit hKc hPK ρ μG H E` takes a measure `μG` on `G(F)`, a subgroup
`H` and an element `E` of the actual rational Schwartz space. It is the conjunction
of:

1. `E ∈ rationalCuspidalLevel hKc hPK ρ H`, that is `E ∈ °C_H`;
2. `∀ x, conj (E x) = E x`, so `E` is real-valued;
3. `∀ x, E x⁻¹ = E x`;
4. `∀ x, E x ≠ 0 → x ∈ rationalCommonNormKernel G`, so `E` is supported in `G¹`;
5. `∀ φ ∈ °C_H, ∀ x, convolution μG φ E x = (μG.real H : ℂ) * φ x`, that is
   `φ ∗ E = mes(H) φ`.

Conjunct 2 has the form of the hypothesis `hE` of
`finiteDimensional_of_kernelAlphaChi`. Conjunct 5 has the form of the reproduction
identity that the Library's `IsKernelAlphaChiSpace` asks for, once
`(μH Set.univ).toReal` is rewritten by `comap_subtype_univ_toReal`. Conjuncts 1, 3
and 4 are the inputs the source uses for `α(·, g₂) ∈ °C_H` and for the diagonal
computation of p. 329. How unit 2 consumes them is decided in unit 2. This module
proves no finiteness.

### The characteristic function (definition, proved formula)

`rationalSubgroupIndicator hKc hPK ρ μG H` is, for a compact open subgroup `H`, the
element `mes(H) • ε_H` of the actual rational Schwartz space. Here `ε_H` is the
Library's `Space.normalizedIndicator`, equal to `mes(H)⁻¹ 1_H`.
`rationalSubgroupIndicator_apply` proves that for a Haar measure `μG` this element
is the function `1_H`, the source's `e`.

### The named laws (definitions; open hypotheses)

Each law is a `Prop` about the linear operator `P`. The laws are stated for
functions: they take the transformed function `f'` together with a pointwise
description of it. This means no check operator, twist operator or translation
operator on the Schwartz space has to be named. An operator-level identity for an
actual operator should give the corresponding law by extensionality, but this
module does not prove that.

| Law | Statement | Source |
| --- | --- | --- |
| `RationalDegreeZeroRangeLaw` | `∀ f, P f ∈ rationalCuspidalSubmodule hKc hPK ρ` | inclusion of the image in the kernel, Lemma VIII.2.1 |
| `RationalDegreeZeroTranslationLaw` | `(∀ x, f' x = f (a x b)) → ∀ x, P f' x = P f (a x b)` | "relation évidente", p. 328 |
| `RationalDegreeZeroConjLaw` | `(∀ x, f' x = conj (f x)) → ∀ x, P f' x = conj (P f x)` | Remark VIII.2.2 |
| `RationalDegreeZeroCheckLaw` | `(∀ x, f' x = f x⁻¹) → ∀ x, P f' x = P f x⁻¹` | Remark VIII.2.2 |
| `RationalDegreeZeroTwistLaw` | for `χ ∈ rationalUnitaryUnramifiedCharacters G`: `(∀ x, f' x = f x * χ x) → ∀ x, P f' x = P f x * χ x` | Remark VIII.2.2 |
| `RationalDegreeZeroLeftConvolutionLaw μG` | `∀ f₁ ∈ rationalCuspidalSubmodule, ∀ f₂ x, convolution μG f₁ (P f₂) x = convolution μG f₁ f₂ x` | left identity of Lemma VIII.2.3 |

### The derivation (proved)

The following hold for a Haar measure `μG`, a compact open subgroup `H` and any
linear `P`:

* `rationalSubgroupIndicator_mul_mul`: `e(x) = e(a x b)` for `a, b ∈ H`.
* `degreeZero_rationalSubgroupIndicator_mem_level`: the range law and the
  translation law give `P e ∈ °C_H`.
* `conj_degreeZero_rationalSubgroupIndicator`: the conjugation law gives
  `conj (P e x) = P e x`, since `ē = e`.
* `degreeZero_rationalSubgroupIndicator_inv`: the check law gives
  `P e x⁻¹ = P e x`, since `eˇ = e`.
* `degreeZero_rationalSubgroupIndicator_support`: the twist law gives
  `P e x ≠ 0 → x ∈ G¹`. Compact subgroups lie in `G¹`
  (`compactSubgroup_le_rationalCommonNormKernel`), so `χ e = e` for every `χ` in
  `Im X(G)`. Hence `P e · (1 - χ) = 0`, and `exists_unitaryUnramified_ne_one`
  gives the result.
* `convolution_degreeZero_rationalSubgroupIndicator`: the left convolution law gives
  `φ ∗ P e = φ ∗ e = mes(H) φ` for `φ ∈ °C_H`, by
  `convolution_indicator_of_rightInvariant`.
* `isRationalCuspidalUnit_of_degreeZeroLaws`: the six laws together give
  `IsRationalCuspidalUnit hKc hPK ρ μG H.toSubgroup (P e)`.

## Open hypotheses and their owners

This unit assumes no same-rank finiteness, no same-rank reconstruction, no
VIII.4.1 target and no dimension bound. The following inputs stay open.

* **The actual operator `degreeZero`** (`f ↦ f - κ(properFourier f)`), conditional on
  the strictly-smaller-rank finiteness and synthesis-reconstruction predicates.
  Owner: **Task 7277** (construction unit 1). Global well-founded assembly of these
  rank-restricted inputs: **Task 3642**.
* `RationalDegreeZeroRangeLaw` for `degreeZero`. Owner: **Task 7277** (VIII.2.1
  comparison target). The law is stated for the Library's `rationalCuspidalSubmodule`,
  the kernel used by the closed VIII.4.1 target. If Task 7277 states VIII.2.1 for
  another presentation of the intrinsic kernel, the comparison between the two is
  also needed; **Task 7252** owns the intrinsic kernel.
* `RationalDegreeZeroConjLaw`, `RationalDegreeZeroCheckLaw` and
  `RationalDegreeZeroTwistLaw` for `degreeZero`. Owner: **Task 7277** (VIII.2.2
  targets). The twist target there uses the Library's twisting action and its
  character group. Matching those with `rationalUnitaryUnramifiedCharacters G` is
  part of the instantiation below.
* `RationalDegreeZeroLeftConvolutionLaw` for `degreeZero` and a Haar measure `μG`.
  Owner: **Task 7277** (VIII.2.3 left target `f₁ ∗ f₂ = f₁ ∗ degreeZero(f₂)`).
* `RationalDegreeZeroTranslationLaw` for `degreeZero`. This is **not** among Task
  7277's listed VIII.2.1–VIII.2.3 targets, and **no task currently owns it**. It is
  the source's "relation évidente" and follows from the translation covariance of
  the Fourier transform and of synthesis. It must be supplied, as a target of a
  Task 7277 successor or within Task 7439, before the instantiation below can be
  completed.
* **Instantiation** (`P := degreeZero` and discharge of the six laws from the
  published targets). Owner: **Task 7439** (this task, unit 3 second layer), after
  Task 7277 publishes the operator and its targets.
* **Consumption** of `IsRationalCuspidalUnit` in the kernel step (level finiteness
  through `IsKernelAlphaChiSpace`). Owner: **Task 7439**, unit 2 (Worker 825).
