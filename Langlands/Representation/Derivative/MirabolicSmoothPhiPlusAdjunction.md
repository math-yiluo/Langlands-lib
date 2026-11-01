# The adjunctions Φ⁻ ⊣ Φ̂⁺ and Ψ⁻ ⊣ Ψ⁺

Author: Worker 749.

This module proves two adjunctions of Bernstein–Zelevinsky (1977) §3.2. It
uses the actual published functors: the normalized minus functors `Φ⁻`, `Ψ⁻`
of `Langlands.Representation.Derivative.MirabolicMinus`, the normalized
`Ψ⁺` of `Langlands.Representation.Derivative.MirabolicPlusNormalization`,
and the smooth `Φ̂⁺` of the companion module
`Langlands.Representation.Derivative.MirabolicSmoothPhiPlus`. Each
adjunction is an explicit complex-linear equivalence of intertwiner spaces,
and naturality in both arguments is proved. The equivalences are:

- `phiHatPlusAdjunction T ψ n A σ :
  Hom(A, Φ̂⁺ σ) ≃ₗ[ℂ] Hom(Φ⁻ A, σ)` (§3.2(c), `Φ⁻` is left adjoint to
  `Φ̂⁺`). It sends `Φ` to the map `q(v) ↦ Φ(v)(1)` and has inverse
  `B ↦ (v ↦ (x ↦ B(q(x • v))))`;
- `psiPlusAdjunction T n A θ : Hom(A, Ψ⁺ θ) ≃ₗ[ℂ] Hom(Ψ⁻ A, θ)` (§3.2(b),
  first part, `Ψ⁻` is left adjoint to `Ψ⁺`). It sends `f` to the map
  `q(v) ↦ f(v)` and has inverse `B ↦ B ∘ q`.

Here `q` is the published quotient map onto the localization, and `Hom`
is the space `Representation.IntertwiningMap` of complex-linear
intertwiners. No exactness is used or stated. The module does not prove the
second part of §3.2(b) (`Φ⁺` left adjoint to `Φ⁻`), the vanishing
composites §3.2(d), the unit and counit statements §3.2(e,f), or Remark 3.3.

Its only direct import is
`Langlands.Representation.Derivative.MirabolicSmoothPhiPlus`. No existing
Library file is changed.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
source `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
PDF page is the printed page minus 439.

- §1.8(a), printed p.444/PDF5: the induced `I_(U,θ)(ρ)` and compactly
  induced `i_(U,θ)(ρ)`, with covariance `f(umg) = θ(u) mod_U^(1/2)(m) ρ(m)(f(g))`
  and right translation (see the companion module).
- §1.8(b), printed pp.444–445/PDF5–6: for `(π, E) ∈ Alg G`, `E(U, θ)` is
  spanned by the vectors `π(u)ξ − θ(u)ξ`, `r_(U,θ)(E) = E/E(U, θ)`, and `M`
  acts by `δ(m)(ξ + E(U, θ)) = mod_U^(-1/2)(m) (π(m)ξ + E(U, θ))`.
- §1.8, last paragraph, printed p.445/PDF6: if `MU = G`, then
  `I_(U,θ)(ρ) = i_(U,θ)(ρ)` acts on the same space as `ρ`.
- §1.9(b), printed p.445/PDF6: "The functor `r_(U,θ)` is left adjoint to
  `I_(U,θ)`", that is, `Hom(r_(U,θ)(π), ρ) = Hom(π, I_(U,θ)(ρ))`
  naturally. The source proves this in its reference [1], chap. I, and adds
  that the `mod^(1/2)` factors must be checked to be compatible.
- §3.2, printed p.451/PDF12: `Ψ⁻ = r_(V,1)`, `Φ⁻ = r_(V,θ)`,
  `Ψ⁺ = i_(V,1)`, `Φ⁺ = i_(V,θ)` and `Φ̂⁺ = I_(V,θ)`. Proposition (b):
  "`Ψ⁻` is left adjoint to `Ψ⁺` and `Φ⁺` is left adjoint to `Φ⁻`";
  (c): "`Φ⁻` is left adjoint to `Φ̂⁺`". Its proof: "(a), (c) and the first
  part of (b) follow from 1.9."

No errata entry for this source is registered in the literature index, and
the Library has no errata note for it.

### Correspondence and route

The published `phiMinus T ψ n` is the source's `r_(V,θ)`: its carrier is
the actual localization
`Jacquet.Localization.Coinvariants A.representation (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n)`,
and `h ∈ P_(n+1)` acts by
`h • q(v) = |det h|^(-1/2) • q(successor h • v)` (published
`phiMinus_action`). The published Haar comparison of
`MirabolicMinusNormalization` identifies `|det|^(-1/2)` with
`mod_V^(-1/2)`. Likewise `psiMinus T n` is `r_(V,1)`, with
`g • q(v) = |det g|^(-1/2) • q(levi g • v)` (`psiMinus_action`). For
`Ψ⁺ = i_(V,1)`, `MU = P_(n+1)`, so by §1.8 the source functor acts on the
space of `θ`; the published `psiPlus` is the inflation of
`|det|^(1/2) ⊗ θ` along the projection `P_(n+1) → GL_n`.

The source deduces §3.2(b,c) from the general §1.9(b). This module does not
formalize §1.9(b). It proves the two special cases directly from the actual
definitions, by evaluation at the identity and descent to the localization,
as follows.

## Φ⁻ ⊣ Φ̂⁺

Fix `A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)` (the
source's `P_(n+2)`) and `σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)`
(the source's `P_(n+1)`).

Character cancellation.
`phiMinusCharacter_mul_phiPlusCharacter_apply` gives
`|det g|^(-1/2) · |det g|^(1/2) = 1` pointwise, from the published
`phiPlusCharacter_mul_phiMinusCharacter`;
`psiMinusCharacter_mul_psiPlusCharacter_apply` is the analogue for `Ψ`.
This is the compatibility of the `mod^(1/2)` factors that §1.9 asks for.

Forward map.

- `phiHatPlusEvalOne T ψ n A σ Φ : A →ₗ[ℂ] σ` is `v ↦ Φ(v)(1)`, the
  value at the identity in the normalized evaluation of the companion
  module. `phiHatPlusEvalOne_apply` records the formula.
- `phiHatPlusEvalOne_translate`: `Φ(g • v)(1) = Φ(v)(g)`, by equivariance
  of `Φ` and right translation.
- `phiHatPlusEvalOne_radical`: for `u` in the radical `V_(n+2)`,
  `Φ(u • v)(1) = Θ(u) • Φ(v)(1)` with `Θ = T.mirabolicTheta ψ n`. This
  follows from the radical covariance of `Φ̂⁺`. The published `thetaPlus`
  restricts on the radical to a character that agrees definitionally with
  `T.mirabolicTheta ψ n`.
- `phiHatPlusEvalOne_successor`:
  `Φ(successor g • v)(1) = |det g|^(1/2) • σ(g)(Φ(v)(1))`, and
  `phiHatPlusEvalOne_phiMinus_action` combines it with the cancellation:
  `|det h|^(-1/2) • Φ(successor h • v)(1) = σ(h)(Φ(v)(1))`.
- `phiHatPlusAdjForward T ψ n A σ Φ` is the descent of `phiHatPlusEvalOne`
  through the published `Jacquet.Localization.lift`, allowed by
  `phiHatPlusEvalOne_radical`. It is an intertwiner for the normalized
  `Φ⁻` action by the previous item; the check uses
  `Jacquet.Localization.hom_ext` on the generators `q(v)`.
  `phiHatPlusAdjForward_mk`: `q(v) ↦ Φ(v)(1)` (`rfl`).

Backward map.

- `phiMinusAdjValue T ψ n A σ B : A →ₗ[ℂ] σ` is `v ↦ B(q(v))`.
  `phiMinusAdjValue_radical`: `B(q(u • v)) = Θ(u) • B(q(v))`, from the
  published `phiMinusQuotient_radical`. `phiMinusAdjValue_successor`:
  `B(q(successor g • w)) = |det g|^(1/2) • σ(g)(B(q(w)))`, from equivariance
  of `B`, `phiMinus_action` and the cancellation.
- `phiMinusAdjValue_covariant`: the function `x ↦ B(q(x • v))` satisfies
  the normalized covariance of `Φ̂⁺(σ)`. For `q₀ ∈ Q`,
  `B(q(q₀ x • v)) = thetaPlus(q₀) • |det(plusProjection q₀)|^(1/2) • σ(plusProjection q₀)(B(q(x • v)))`.
  The proof writes `q₀ = plusRadical u * plusSuccessor g` (published
  `plus_eq_plusRadical_mul_plusSuccessor`) and applies the two previous
  laws.
- `phiHatPlusOrbitMap T ψ n A σ B` is the intertwiner from `A` into the
  published full covariant-function representation
  `Induction.equivariantAction Q τ''` sending `v` to this function. Here
  `τ'' = plusTwistRepresentation ψ n (Langlands.twist (phiPlusCharacter T n) σ.representation)`.
  `phiHatPlusAdjBackward T ψ n A σ B` is its corestriction to the smooth
  vectors by the published `smoothLift`, which applies because `A` is
  smooth. The result is an intertwiner `A → Φ̂⁺(σ)`.
  `phiHatPlusAdjBackward_eval`: the value at `x` of the image of `v` is
  `B(q(x • v))` (`rfl`).

The equivalence.

`phiHatPlusAdjunction T ψ n A σ` is the linear equivalence with these two
maps. The left inverse law is `Φ(v)(x) = Φ(x • v)(1)`
(`phiHatPlusEvalOne_translate`) together with
`phiHatPlusNormalizedEval_injective`. The right inverse law, additivity and
homogeneity are checked on the generators `q(v)`, by
`Jacquet.Localization.hom_ext`; the right inverse law reduces to
`B(q(1 • v)) = B(q(v))`. The formula lemmas are
`phiHatPlusAdjunction_mk` (`Φ ↦ (q(v) ↦ Φ(v)(1))`) and
`phiHatPlusAdjunction_symm_eval` (`B ↦ (v ↦ (x ↦ B(q(x • v))))`), both
`rfl`.

Naturality.

- `phiHatPlusAdjunction_comp_left`: for `f : A' ⟶ A`, the adjunct of
  `Φ ∘ f` is the adjunct of `Φ` composed with `Φ⁻ f`;
- `phiHatPlusAdjunction_comp_right`: for `g : σ ⟶ σ'`, the adjunct of
  `Φ̂⁺ g ∘ Φ` is `g` composed with the adjunct of `Φ`.

Both are checked on the generators `q(v)`, where they hold by definition.

## Ψ⁻ ⊣ Ψ⁺

Fix `A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier)` (the source's
`P_(n+1)`) and
`θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier)`.

- `psiPlusAdj_radical`: an intertwiner `f : A → Ψ⁺ θ` satisfies
  `f(u • v) = f(v)` for `u` in the radical `V_(n+1)`, stated with the
  trivial character `1` of the localization, since the radical acts
  trivially on `Ψ⁺ θ` (published `psiPlus_radical`).
- `psiPlusAdjForward T n A θ f` is the descent of `f` through
  `Jacquet.Localization.lift`. It intertwines the normalized `Ψ⁻` action
  with `θ`, by `psiMinus_action`, `psiPlus_levi` and the cancellation.
  `psiPlusAdjForward_mk`: `q(v) ↦ f(v)` (`rfl`).
- `psiPlusAdjBackward T n A θ B` is `B ∘ q`. It is an intertwiner into
  `Ψ⁺ θ`: write `g = radicalElement(·) * levi (projection g)` (published
  `eq_radicalElement_mul_levi`), kill the radical factor by
  `psiMinusQuotient_radical`, and move the Levi factor through `B` by
  `psiMinus_action` and the cancellation. `psiPlusAdjBackward_apply`:
  `v ↦ B(q(v))` (`rfl`).
- `psiPlusAdjunction T n A θ` is the linear equivalence with these maps.
  Both inverse laws, additivity and homogeneity hold on generators by
  definition. `psiPlusAdjunction_mk` and `psiPlusAdjunction_symm_apply`
  record the formulas, and `psiPlusAdjunction_comp_left` and
  `psiPlusAdjunction_comp_right` are naturality in `A` and in `θ`, stated
  as for `Φ`.

## Parameters, topology and universes

Throughout, `p : ℕ` is prime (`[Fact p.Prime]`), `F : PadicField.{uF} p`,
`T : F.TopologicalData` is an arbitrary supplied topological realization,
and every topological statement installs `letI := T.topology` (and
`T.generalLinearTopologicalGroup (n + 1 + 1)` for the orbit map into the
induced space). The additive character is
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`;
its nontriviality is not used. Every `n : ℕ` is allowed, with no case split.

The universes of `A` (`uA`) and of `σ`, `θ` (`uV`) are independent. The
inspected level parameters of `phiHatPlusAdjunction` and
`psiPlusAdjunction` are `uA, uV, uF`. The main types are:

```lean
phiHatPlusAdjunction.{uA, uV, uF} : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  (T : F.TopologicalData) → (ψ : UnitaryAdditiveCharacter F.Carrier) → (n : ℕ) →
  (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)) →
  (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
  A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation ≃ₗ[ℂ]
    ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation
psiPlusAdjunction.{uA, uV, uF} : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  (T : F.TopologicalData) → (n : ℕ) →
  (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier)) →
  (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) →
  A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation ≃ₗ[ℂ]
    ((psiMinus T n).obj A).representation.IntertwiningMap θ.representation
```

`Φ⁻` keeps the universe `uA`, while `Φ̂⁺` sends `uV` to `max uF uV`. So the
two functors are not endofunctors of one universe-fixed category pair. The
adjunction is therefore stated as a natural linear equivalence of
intertwiner spaces across universes, not as a Mathlib
`CategoryTheory.Adjunction`. No universe is resized.

All main declarations depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The two equivalences are the source's adjunctions §3.2(b) (first part) and
§3.2(c), with the source's normalizations: `mod_V^(-1/2)` on `Φ⁻`, `Ψ⁻`
and `mod_V^(1/2)` on `Φ̂⁺`, `Ψ⁺`, realized as `|det|^(∓1/2)` through the
published Haar comparisons. The source derives them from the general §1.9(b)
and its reference [1]. The Lean proofs here are direct and internal: they
evaluate at the identity and descend to the localization, using only the
cited Library constructions and Mathlib. No other original-literature
theorem is asserted.

## Import and dependency audit

### Complete import inventory

The recursive `Langlands` import closure of this module was computed by
following every `import` line, starting from this module, through the
companion module and the Library at base
`b22e185743f7c318f709e14e422801f4360105d5`. It consists of exactly 84
modules:

1. this module, `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`,
   whose only direct import is the companion module;
2. the companion module `Langlands.Representation.Derivative.MirabolicSmoothPhiPlus`,
   submitted separately as candidate
   `2546568e-f4b1-45e8-8b17-05a43ca7d49b` and not yet in the Library at
   this base;
3. the following 82 published, paired Library modules at this base. The
   16 entries marked "(statement)" contain Prop-valued statement
   definitions.

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.BlockModulus`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicModulusProof`
- `Langlands.Group.GL.MirabolicModulusStatement` (statement)
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement` (statement)
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.Group.HaarModulus`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.HarmonicAnalysis.PadicHaarScalingStatement` (statement)
- `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement` (statement)
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Abelian`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Derivative.MirabolicMinusNormalization`
- `Langlands.Representation.Derivative.MirabolicPlus`
- `Langlands.Representation.Derivative.MirabolicPlusNormalization`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Filtration.IsoTransport`
- `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`
- `Langlands.Representation.Geometric.CompactSmoothComparison`
- `Langlands.Representation.Geometric.SmoothSupportFiltration`
- `Langlands.Representation.Induction.CompactQuotientProof`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.Equivalences`
- `Langlands.Representation.Induction.Parabolic`
- `Langlands.Representation.Induction.StructuralStatement` (statement)
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement` (statement)
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement` (statement)
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.BasicProof`
- `Langlands.Representation.Smooth.SmoothPart.BasicStatement` (statement)
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement` (statement)
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement` (statement)
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement` (statement)
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement` (statement)
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement` (statement)
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement` (statement)
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement` (statement)
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.CompactOpen.ConjugationStabilizer`
- `Langlands.Topology.CompactOpen.NeighborhoodBasis`
- `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement` (statement)
- `Langlands.Topology.Nonarchimedean.Subgroup`

The closure contains no other project module; everything else imported is
Mathlib.

### Statement definitions and proved inputs

The 16 statement modules supply Prop-valued definitions, which are targets,
not proved inputs. No declaration of this module or of the companion takes
any of them, or any other Prop-valued statement, as a hypothesis. In
particular, `Langlands.Representation.Induction.StructuralStatement` defines
Frobenius-reciprocity, induction-exactness and open-subgroup-adjunction
clauses as propositions. This module neither assumes nor uses them: both
adjunctions are constructed directly. The Library results this module uses
are published theorems and definitions with complete Lean proofs.

### Actual proof dependencies

The proofs use only these imported declarations, together with Mathlib
(`Representation.IntertwiningMap`, linear maps and equivalences, basic
category theory):

- companion module: `phiHatPlus`, its normalized evaluation, covariance,
  open-stabilizer and constructor API, and its action and map laws;
- `Derivative.MirabolicMinus`: the published functors `phiMinus` and
  `psiMinus`, their quotient maps `phiMinusQuotient` and `psiMinusQuotient`,
  the `_radical` and `_action` laws, and the characters `phiMinusCharacter`
  and `psiMinusCharacter`. These are the definitions of the functors and
  their basic laws, not an exactness result;
- `Derivative.MirabolicPlusNormalization`: `phiPlusCharacter`,
  `psiPlusCharacter`, the functor `psiPlus` with `psiPlus_radical`,
  `psiPlus_levi` and `psiPlus_action`, and the published character
  cancellations `phiPlusCharacter_mul_phiMinusCharacter` and
  `psiPlusCharacter_mul_psiMinusCharacter`;
- `Derivative.MirabolicPlus`: `plusTwistRepresentation` and
  `plusTwistRepresentation_plusRadical_mul_plusSuccessor`;
- `Derivative.MirabolicCharacter`: the character `mirabolicTheta`;
- `Group.GL.MirabolicProjection`: `plusSubgroup`, `plusRadical`,
  `plusSuccessor`, `plusRadical_val`, `plusSuccessor_val` and
  `plus_eq_plusRadical_mul_plusSuccessor`;
- `Jacquet.Localization`: `lift` and `hom_ext`, and through `phiMinus`
  and `psiMinus` the localization carrier `Coinvariants`;
- `Induction.Definitions`: `equivariantAction`;
- `Smooth.SmoothPart.Definitions`: `smoothLift`.

The companion module itself uses the smooth induction of
`Induction.Definitions` (`SmoothFunctions`, `smoothInductionFunctor`,
`smoothFunctionOf`), `Induction.Equivalences`, the compact-to-smooth
inclusion `Induction.compactSmoothInclusion` of
`Geometric.CompactSmoothComparison`, the published radical Haar comparison
`phiPlusHaarHalf_eq` of `Derivative.MirabolicPlusNormalization`, the twist
functor `SmoothRep.twistFunctor` and `SmoothRep.mono_iff_injective` of
`Category.Abelian`. The remaining modules of the inventory enter only
through the imports of these modules.

### Condition-by-condition exclusion audit

The conditions are those of the complete inherited exclusion set in the
context of task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4` revision 2, from
"Complete inherited exclusion set" to the end. A module can depend only on
declarations in its import closure, so it suffices to check that no
excluded statement, proof or consequence lies in the 84 modules above and
that no excluded conclusion is assumed.

1. **Exclusion list of `b711af72` (objective).** Ordered-socle existence
   `23189526`, socle exhaustion `f3a69bc8`, analytic segment classification
   `aca8805b`, segment-socle product irreducibility `23e98d90`, the final
   criterion `2ae5cbe5`, `AdjacentUnlinkedSegmentSocleSwap`,
   `TwoSegmentSocleCommutation`, the special-head criterion `8364e73f`,
   special-head exhaustion `3bfb61fa`, ordered special-head existence
   `ebea9a8a`, quotient coverage `20e4e1c6`, tempered block uniqueness
   `52e97845`, `SquareIntegrableLanglandsClassification` / `1cb45da2`,
   square-integrable exhaustion `cd8ab97c`, regular exhaustion `bf433f0a`,
   `GenericSegmentProductUniqueness` / `30341ae4`, ordered conversion
   `8252833d` and forward special-segment square-integrability `5eece9e8`:
   satisfied. The inventory contains no `Classification`, segment,
   multisegment, socle, head, tempered, square-integrability or exhaustion
   module, and no such conclusion is assumed.
2. **Operator-paused minus exactness `b65bc667`.** Satisfied. The statement
   module `Derivative.MirabolicMinusExactnessStatement` is not in the
   closure, exactness of `Φ⁻` or `Ψ⁻` is neither proved nor assumed, and the
   task is not resumed or bypassed. The adjunctions need no exactness.
3. **Detection-unit restrictions.** The combined Ze80 §5.4 reduction, its
   strong-indecomposability conclusion (`ff4738d8`), the nonadjacent
   product `3c9849a4` and the full product structure `ab61f565`: satisfied.
   No such module is in the closure, and none of these is assumed.
4. **Additional nonadjacent-consumer list.** `67279e36`, `4ca79bbd`,
   `aca8805b`, `SegmentSpecialEssentialSquareIntegrability` / `5eece9e8`,
   `3bfb61fa`, `ebea9a8a`, `20e4e1c6`, `8252833d`, `52e97845`, `1cb45da2`,
   `cd8ab97c`, `bf433f0a`, `8364e73f`, `30341ae4`,
   `OrderedMultisegmentSocleExistence` / `23189526`,
   `MultisegmentSocleExhaustion` / `f3a69bc8`,
   `SegmentSocleProductIrreducibility` / `2ae5cbe5`, adjacent socle
   commutation `e3634665`, `SegmentFullJacquetFormula` / `ed48ae06` and its
   proof, `SegmentHeadJacquetFormula` / `55ad1e10`,
   `SegmentSocleJacquetFormula` / `b95105c6` and
   `SegmentSpecialJacquetExponentNormFormula` / `92aea10f`: satisfied. The
   only Jacquet modules in the closure are `Jacquet.Coinvariants`,
   `Jacquet.Localization`, `Jacquet.PositiveCharacter` and
   `Jacquet.SmoothTwist`. They contain general coinvariant and localization
   constructions and character twists, not segment Jacquet formulas.
5. **Full-formula consumer restrictions.** No Ze80 §3.5 or §9.6 segment
   derivative formula, no segment product criterion (Ze80 4.2, 9.7), no
   analytic or square-integrability result (Ze80 9.3) and no classification
   or exhaustion theorem: satisfied. No Zelevinsky 1980 result is used. No
   derivative result of BZ77 or anyone else is assumed. The only derivative
   inputs are the published functor constructions and character
   comparisons listed above, all with published Lean proofs. The segment-socle
   part of task `8e5b4563` is not used.
6. **Shared upstream scope of `3238f371` revision 2.** Satisfied.
   `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, the
   all-character single-block conclusion `62de5903` and their consequences
   are not in the closure or assumed. No missing proof is replaced by a
   consumer assumption. Worker 127 was not contacted. The parent list
   (`30341ae4`, `3bfb61fa`, `ebea9a8a`, `20e4e1c6`, `8252833d`, `52e97845`,
   `1cb45da2`, `cd8ab97c`, `bf433f0a`) is covered by items 1 and 4.
7. **Independence section of `2e5183b1` revision 2.**
   `UnlinkedSegmentSocleProductIrreducible`,
   `LinkedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSoclePairReducible` (`23e98d90`, `a55c4267`, `8fa9f68b`),
   `JuxtaposedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSocleReverseProductQuotientHom` (`7ff2a1e9`),
   `SegmentSocleProductIrreducibility` (`2ae5cbe5`),
   `AdjacentUnlinkedSegmentSocleSwap` (`e3634665`, `cded83f3`),
   `TwoSegmentSocleCommutation` (`426911b4`, `66e3b87c`),
   `LinkedSegmentSocleGluing` (`c84cd52c`, `6780b79c`), the remaining tasks
   of that list (covered by items 1 and 4) and `SegmentHeadProductIrreducibility`
   (`8364e73f`): satisfied, none in the closure. Of the shared lower inputs
   named there, only the derivative functor constructions `Φ⁻`, `Ψ⁻`, `Ψ⁺`
   are used. Their independence is checked by this inventory, since their
   modules and closures lie in it. No exactness, Leibniz filtration,
   geometric lemma, cuspidal-support or finite-length module is in the
   closure. `Geometric.ClosedSubgroupDefinitions`,
   `Geometric.SmoothSupportFiltration` and `Geometric.CompactSmoothComparison`
   are support-filtration definitions and the compact-to-smooth inclusion,
   not the BZ77 geometric lemma.
8. **BZ77-only upstream restrictions.** No segment derivative formula,
   segment-socle or head existence, Jacquet formula or segment
   classification; no part (b), (d), (e), (f) of the parent six-statement
   contribution; no `TwoSupercuspidalNonadjacentProductIrreducible`
   (`3c9849a4`) or `TwoSupercuspidalProductStructure` (`ab61f565`):
   satisfied, none in the closure or assumed. Its additional consumer list
   is the list of item 4.
9. **Whittaker-finiteness independence.**
   `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` and parent
   `5ab445dc`, `LeviCuspidalCoinvariantFinitenessStatement` and proof task
   `3ff5c8fb`, their consequences, and the mirabolic finite-length route of
   task `5428fe2c`: satisfied. No finiteness or finite-length module is in
   the closure. The closure contains two Whittaker modules.
   `Whittaker.Algebraic` defines left-equivariant functions, equivariant
   functionals and coefficient models with their elementary laws.
   `Whittaker.GeneralLinear` defines the standard character
   `ψ(Σ u_(i,i+1))`, its inverse and scaled variants, GL coefficient
   models and the predicate `IsGeneric`. Their own imports are
   `MatrixCoefficient`, `Smooth.Definitions`, `Group.GL.UpperUnipotent` and
   `HarmonicAnalysis.Basic` modules. They enter the closure only through
   `Derivative.MirabolicCharacter`, which identifies the mirabolic
   character `θ` with a restriction of the standard character
   (`theta_eq_standardCharacter_comp`). They contain no coinvariant
   finiteness statement or theorem, and none of their declarations is used
   here except through that character.

The proofs use no `sorry`, `admit` or new axiom. This inventory and audit
are an author audit, not independent acceptance evidence.
