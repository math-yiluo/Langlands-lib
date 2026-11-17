import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionFamily
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.UnramifiedCharacters

/-! # The cuspidal unit `°e` of the proof of Proposition VIII.4.1

Waldspurger's proof of Proposition VIII.4.1 applies the degree-zero projection
`f ↦ °f` of VIII.2 to the characteristic function `e = 1_H` of a compact open subgroup `H`.
The resulting function `°e` is the unit from which the reproducing kernel `α_χ` is built.
This module states the properties of `°e` used by the kernel step as the predicate
`IsRationalCuspidalUnit`, and derives them from explicit laws of an arbitrary linear operator
`P` on the actual rational Schwartz space, each law named as a separate proposition.
No law is proved here for the actual degree-zero projection of Task 7277; that operator does
not yet exist in the Library.

Two facts about the actual group are proved: unitary unramified characters separate the points
of `G / G¹` (`exists_unitaryUnramified_ne_one`), and the characteristic function of `H`
reproduces right `H`-invariant functions under convolution
(`convolution_indicator_of_rightInvariant`).
-/

noncomputable section

universe u uΓ

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General
open Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Indicator

variable {Γ : Type uΓ} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

/-- `φ ∗ 1_H = mes(H) φ` for a right `H`-invariant `φ` and a left-invariant measure. This is the
last equality `φ ∗ e = mes(H) φ` in the proof of Proposition VIII.4.1. -/
theorem convolution_indicator_of_rightInvariant (mu : Measure Γ) [mu.IsMulLeftInvariant]
    {H : Subgroup Γ} (hH : MeasurableSet (H : Set Γ)) {φ : Γ → ℂ}
    (hφ : ∀ h ∈ H, ∀ x, φ (x * h) = φ x) (x : Γ) :
    convolution mu φ ((H : Set Γ).indicator fun _ => (1 : ℂ)) x =
      (mu.real (H : Set Γ) : ℂ) * φ x := by
  rw [convolution_apply, ← integral_mul_left_eq_self _ x]
  have hpt : ∀ k : Γ,
      φ (x * k) * (H : Set Γ).indicator (fun _ => (1 : ℂ)) ((x * k)⁻¹ * x) =
        φ x * (H : Set Γ).indicator (fun _ => (1 : ℂ)) k := by
    intro k
    have e : (x * k)⁻¹ * x = k⁻¹ := by group
    rw [e]
    by_cases hk : k ∈ H
    · rw [Set.indicator_of_mem (show k⁻¹ ∈ (H : Set Γ) from H.inv_mem hk),
        Set.indicator_of_mem (show k ∈ (H : Set Γ) from hk), hφ k hk x]
    · have hk' : k⁻¹ ∉ (H : Set Γ) := fun h => hk (by simpa using H.inv_mem h)
      rw [Set.indicator_of_notMem hk', Set.indicator_of_notMem (show k ∉ (H : Set Γ) from hk),
        mul_zero, mul_zero]
  simp_rw [hpt]
  rw [integral_const_mul, integral_indicator hH, setIntegral_const, Complex.real_smul, mul_one,
    mul_comm]

omit [MeasurableMul Γ] in
/-- The total mass of the restriction `μ_H = μ.comap (↑)` of `μ` to a measurable subgroup is
`μ(H)`; with this choice of `μ_H` the constant `(μ_H Set.univ).toReal` of the Library's kernel
`kernelAlphaChi` is `mes(H)`. -/
theorem comap_subtype_univ_toReal (mu : Measure Γ) {H : Subgroup Γ}
    (hH : MeasurableSet (H : Set Γ)) :
    ((mu.comap ((↑) : H → Γ)) Set.univ).toReal = mu.real (H : Set Γ) := by
  have he : MeasurableEmbedding ((↑) : H → Γ) := MeasurableEmbedding.subtype_coe hH
  rw [he.comap_apply, Set.image_univ, Subtype.range_coe_subtype]
  rfl

end Indicator

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Separation

variable (G) in
/-- Waldspurger's `Im X(G)`: the actual unitary unramified characters of `G(F)`, trivial on
`G¹ = rationalCommonNormKernel G`. -/
abbrev rationalUnitaryUnramifiedCharacters : Subgroup (rationalPoints G →ₜ* ℂˣ) :=
  unitaryUnramifiedCharacters (fun c => (rationalNormCharacters G c).toMul)

omit [LocallyOfFiniteType G.X.hom] in
/-- Unitary unramified characters are trivial on `G¹`. -/
theorem rationalUnitaryUnramified_eq_one_of_mem {χ : rationalPoints G →ₜ* ℂˣ}
    (hχ : χ ∈ rationalUnitaryUnramifiedCharacters G) {x : rationalPoints G}
    (hx : x ∈ rationalCommonNormKernel G) : χ x = 1 :=
  MonoidHom.mem_ker.mp (hχ.1 hx)

omit [LocallyOfFiniteType G.X.hom] in
/-- **Unitary unramified characters separate the points of `G(F) / G¹`**: if `x ∉ G¹`, some
`χ ∈ Im X(G)` has `χ(x) ≠ 1`. If the valuation `n = ord(c(x))` of a rational character `c` at
`x` is nonzero, `χ(g) = exp(π i / n)^{ord(c(g))}` works, since `χ(x) = exp(π i) = -1`. -/
theorem exists_unitaryUnramified_ne_one {x : rationalPoints G}
    (hx : x ∉ rationalCommonNormKernel G) :
    ∃ χ ∈ rationalUnitaryUnramifiedCharacters G, (χ x : ℂ) ≠ 1 := by
  rw [mem_rationalCommonNormKernel_iff_valuation] at hx
  push Not at hx
  obtain ⟨c, hc⟩ := hx
  set n : ℤ := (rationalCharacterValuation G x).toAdd c with hn
  set z : ℂ := (((Real.pi / n : ℝ)) : ℂ) * Complex.I with hz
  let u : ℂˣ := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)
  have hu : ‖(u : ℂ)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  let ord : rationalPoints G →ₜ* Multiplicative ℤ := rationalOrderContinuousCharacter G c
  let ψ : rationalPoints G →ₜ* ℂˣ :=
    { toMonoidHom := (zpowersHom ℂˣ u).comp ord.toMonoidHom
      continuous_toFun :=
        (continuous_of_discreteTopology (f := ⇑(zpowersHom ℂˣ u))).comp ord.continuous }
  have hψ : ∀ g, (ψ g : ℂ) = (u : ℂ) ^ ((rationalCharacterValuation G g).toAdd c) := by
    intro g
    change ((u ^ (ord g).toAdd : ℂˣ) : ℂ) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · intro g hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    change (ψ g : ℂ) = 1
    rw [hψ, (mem_rationalCommonNormKernel_iff_valuation G g).mp hg c, zpow_zero]
  · intro g
    change ‖(ψ g : ℂ)‖ = 1
    rw [hψ, norm_zpow, hu, one_zpow]
  · rw [hψ, ← hn]
    change Complex.exp z ^ n ≠ 1
    rw [← Complex.exp_int_mul, hz]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hc
    have h : (n : ℂ) * ((((Real.pi / n : ℝ)) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [h, Complex.exp_pi_mul_I]
    norm_num

end Separation

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

section Unit

/-- **The properties of `°e` used in the proof of Proposition VIII.4.1**, for a function `E` of
the actual rational Schwartz space, a measure `μG` on `G(F)` and a subgroup `H`:
`E ∈ °C_H`; `E` is real; `E(x⁻¹) = E(x)`; `E` is supported in `G¹`; and
`φ ∗ E = mes(H) φ` for every `φ ∈ °C_H`, with the Library's convolution for `μG`. -/
def IsRationalCuspidalUnit (μG : Measure (rationalPoints G)) (H : Subgroup (rationalPoints G))
    (E : RationalSchwartzSpace hKc hPK ρ) : Prop :=
  E ∈ rationalCuspidalLevel hKc hPK ρ H ∧
    (∀ x, conj (E x) = E x) ∧
    (∀ x, E x⁻¹ = E x) ∧
    (∀ x, E x ≠ 0 → x ∈ rationalCommonNormKernel G) ∧
    ∀ φ ∈ rationalCuspidalLevel hKc hPK ρ H, ∀ x,
      convolution μG (φ : rationalPoints G → ℂ) E x =
        (μG.real (H : Set (rationalPoints G)) : ℂ) * φ x

/-- The characteristic function `e = 1_H` of a compact open subgroup `H` as an element of the
actual rational Schwartz space: `mes(H) ε_H` for the Library's normalized indicator
`ε_H = mes(H)⁻¹ 1_H`. -/
def rationalSubgroupIndicator (μG : Measure (rationalPoints G))
    (H : CompactOpenSubgroup (rationalPoints G)) : RationalSchwartzSpace hKc hPK ρ :=
  (μG.real (H.1 : Set (rationalPoints G)) : ℂ) •
    Space.normalizedIndicator μG (continuous_rationalXi K.isOpen hKc hPK)
      (rationalXi_pos K.isOpen hKc hPK) (continuous_rationalHeight ρ) (rationalHeight_nonneg ρ) H

theorem rationalSubgroupIndicator_apply (μG : Measure (rationalPoints G)) [μG.IsHaarMeasure]
    (H : CompactOpenSubgroup (rationalPoints G)) (x : rationalPoints G) :
    rationalSubgroupIndicator hKc hPK ρ μG H x =
      (H.1 : Set (rationalPoints G)).indicator (fun _ => (1 : ℂ)) x := by
  have hne := Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μG H.1 H.2
  change (μG.real (H.1 : Set (rationalPoints G)) : ℂ) *
      Space.normalizedIndicator μG _ _ _ _ H x = _
  rw [Space.normalizedIndicator_apply, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end Unit

section Laws

variable (P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ)

/-- Range in the intrinsic cuspidal kernel `°C(G)` (the inclusion of the image in the kernel
asserted by Lemma VIII.2.1). -/
def RationalDegreeZeroRangeLaw : Prop :=
  ∀ f, P f ∈ rationalCuspidalSubmodule hKc hPK ρ

/-- Two-sided translation equivariance `°(ρ(g₁) λ(g₂) f) = ρ(g₁) λ(g₂) °f`, the "relation
évidente" of the proof of Proposition VIII.4.1, for functions: if `f'(x) = f(a x b)` for all
`x`, then `(Pf')(x) = (Pf)(a x b)` for all `x`. -/
def RationalDegreeZeroTranslationLaw : Prop :=
  ∀ (a b : rationalPoints G) (f f' : RationalSchwartzSpace hKc hPK ρ),
    (∀ x, f' x = f (a * x * b)) → ∀ x, P f' x = P f (a * x * b)

/-- Commutation with complex conjugation, `°(f̄) = \overline{°f}` (Remark VIII.2.2). -/
def RationalDegreeZeroConjLaw : Prop :=
  ∀ f f' : RationalSchwartzSpace hKc hPK ρ,
    (∀ x, f' x = conj (f x)) → ∀ x, P f' x = conj (P f x)

/-- Commutation with `f ↦ fˇ`, `°(fˇ) = (°f)ˇ` (Remark VIII.2.2). -/
def RationalDegreeZeroCheckLaw : Prop :=
  ∀ f f' : RationalSchwartzSpace hKc hPK ρ,
    (∀ x, f' x = f x⁻¹) → ∀ x, P f' x = P f x⁻¹

/-- Commutation with multiplication by a unitary unramified character, `°(f χ) = (°f) χ` for
`χ ∈ Im X(G)` (Remark VIII.2.2). -/
def RationalDegreeZeroTwistLaw : Prop :=
  ∀ χ ∈ rationalUnitaryUnramifiedCharacters G, ∀ f f' : RationalSchwartzSpace hKc hPK ρ,
    (∀ x, f' x = f x * χ x) → ∀ x, P f' x = P f x * χ x

/-- The left convolution identity of Lemma VIII.2.3, `f₁ ∗ f₂ = f₁ ∗ °f₂` for `f₁ ∈ °C(G)`,
pointwise for the Library's convolution with `μG`. -/
def RationalDegreeZeroLeftConvolutionLaw (μG : Measure (rationalPoints G)) : Prop :=
  ∀ f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ, ∀ (f₂ : RationalSchwartzSpace hKc hPK ρ) x,
    convolution μG (f₁ : rationalPoints G → ℂ) (P f₂) x = convolution μG f₁ f₂ x

end Laws

section Derivation

variable (μG : Measure (rationalPoints G)) [μG.IsHaarMeasure]
  (H : CompactOpenSubgroup (rationalPoints G))
  {P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ}

theorem rationalSubgroupIndicator_mul_mul (a b : rationalPoints G) (ha : a ∈ H.toSubgroup)
    (hb : b ∈ H.toSubgroup) (x : rationalPoints G) :
    rationalSubgroupIndicator hKc hPK ρ μG H x =
      rationalSubgroupIndicator hKc hPK ρ μG H (a * x * b) := by
  rw [rationalSubgroupIndicator_apply, rationalSubgroupIndicator_apply]
  have hiff : a * x * b ∈ H.toSubgroup ↔ x ∈ H.toSubgroup := by
    rw [Subgroup.mul_mem_cancel_right _ hb, Subgroup.mul_mem_cancel_left _ ha]
  by_cases hx : x ∈ H.toSubgroup
  · rw [Set.indicator_of_mem (show x ∈ (H.1 : Set (rationalPoints G)) from hx),
      Set.indicator_of_mem (show a * x * b ∈ (H.1 : Set (rationalPoints G)) from hiff.mpr hx)]
  · rw [Set.indicator_of_notMem (show x ∉ (H.1 : Set (rationalPoints G)) from hx),
      Set.indicator_of_notMem
        (show a * x * b ∉ (H.1 : Set (rationalPoints G)) from fun h => hx (hiff.mp h))]

/-- `°e ∈ °C_H`, from the range law and two-sided translation equivariance. -/
theorem degreeZero_rationalSubgroupIndicator_mem_level
    (hrange : RationalDegreeZeroRangeLaw hKc hPK ρ P)
    (htrans : RationalDegreeZeroTranslationLaw hKc hPK ρ P) :
    P (rationalSubgroupIndicator hKc hPK ρ μG H) ∈ rationalCuspidalLevel hKc hPK ρ H.toSubgroup :=
  ⟨hrange _, fun a ha b hb x =>
    (htrans a b _ _ (rationalSubgroupIndicator_mul_mul hKc hPK ρ μG H a b ha hb) x).symm⟩

/-- `°e` is real: `\overline{°e} = °(ē) = °e`. -/
theorem conj_degreeZero_rationalSubgroupIndicator
    (hconj : RationalDegreeZeroConjLaw hKc hPK ρ P) (x : rationalPoints G) :
    conj (P (rationalSubgroupIndicator hKc hPK ρ μG H) x) =
      P (rationalSubgroupIndicator hKc hPK ρ μG H) x := by
  refine (hconj _ _ (fun y => ?_) x).symm
  rw [rationalSubgroupIndicator_apply]
  by_cases hy : y ∈ (H.1 : Set (rationalPoints G))
  · rw [Set.indicator_of_mem hy, map_one]
  · rw [Set.indicator_of_notMem hy, map_zero]

/-- `°e(x⁻¹) = °e(x)`: `(°e)ˇ = °(eˇ) = °e`. -/
theorem degreeZero_rationalSubgroupIndicator_inv
    (hcheck : RationalDegreeZeroCheckLaw hKc hPK ρ P) (x : rationalPoints G) :
    P (rationalSubgroupIndicator hKc hPK ρ μG H) x⁻¹ =
      P (rationalSubgroupIndicator hKc hPK ρ μG H) x := by
  refine (hcheck _ _ (fun y => ?_) x).symm
  rw [rationalSubgroupIndicator_apply, rationalSubgroupIndicator_apply]
  by_cases hy : y ∈ (H.1 : Set (rationalPoints G))
  · rw [Set.indicator_of_mem hy,
      Set.indicator_of_mem (show y⁻¹ ∈ (H.1 : Set (rationalPoints G)) from H.1.inv_mem hy)]
  · rw [Set.indicator_of_notMem hy,
      Set.indicator_of_notMem (show y⁻¹ ∉ (H.1 : Set (rationalPoints G)) from
        fun h => hy (by simpa using H.1.inv_mem h))]

/-- `°e` is supported in `G¹`: `χ °e = °(χ e) = °e` for `χ ∈ Im X(G)`, since `H ⊆ G¹`; the
characters `Im X(G)` separate the points of `G / G¹`. -/
theorem degreeZero_rationalSubgroupIndicator_support
    (htwist : RationalDegreeZeroTwistLaw hKc hPK ρ P) {x : rationalPoints G}
    (hx : P (rationalSubgroupIndicator hKc hPK ρ μG H) x ≠ 0) :
    x ∈ rationalCommonNormKernel G := by
  by_contra hx1
  obtain ⟨χ, hχ, hχx⟩ := exists_unitaryUnramified_ne_one hx1
  have hHG : H.toSubgroup ≤ rationalCommonNormKernel G :=
    compactSubgroup_le_rationalCommonNormKernel G H.toSubgroup H.2
  have heq := htwist χ hχ (rationalSubgroupIndicator hKc hPK ρ μG H)
    (rationalSubgroupIndicator hKc hPK ρ μG H) (fun y => by
      rw [rationalSubgroupIndicator_apply]
      by_cases hy : y ∈ H.toSubgroup
      · rw [rationalUnitaryUnramified_eq_one_of_mem hχ (hHG hy)]
        simp
      · rw [Set.indicator_of_notMem (show y ∉ (H.1 : Set (rationalPoints G)) from hy),
          zero_mul]) x
  have h0 : P (rationalSubgroupIndicator hKc hPK ρ μG H) x * (1 - (χ x : ℂ)) = 0 := by
    rw [mul_sub, mul_one, ← heq, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact hx h
  · exact hχx (sub_eq_zero.mp h).symm

/-- Reproduction `φ ∗ °e = φ ∗ e = mes(H) φ` for `φ ∈ °C_H` (Lemma VIII.2.3). -/
theorem convolution_degreeZero_rationalSubgroupIndicator
    (hconv : RationalDegreeZeroLeftConvolutionLaw hKc hPK ρ P μG)
    {φ : RationalSchwartzSpace hKc hPK ρ} (hφ : φ ∈ rationalCuspidalLevel hKc hPK ρ H.toSubgroup)
    (x : rationalPoints G) :
    convolution μG (φ : rationalPoints G → ℂ) (P (rationalSubgroupIndicator hKc hPK ρ μG H)) x =
      (μG.real (H.1 : Set (rationalPoints G)) : ℂ) * φ x := by
  rw [hconv φ hφ.1 _ x]
  have he : ((rationalSubgroupIndicator hKc hPK ρ μG H : RationalSchwartzSpace hKc hPK ρ) :
      rationalPoints G → ℂ) = (H.1 : Set (rationalPoints G)).indicator (fun _ => (1 : ℂ)) :=
    funext (rationalSubgroupIndicator_apply hKc hPK ρ μG H)
  rw [he]
  exact convolution_indicator_of_rightInvariant μG H.1.isOpen.measurableSet
    (fun h hh y => by simpa using hφ.2 1 H.toSubgroup.one_mem h hh y) x

/-- **The cuspidal unit of Proposition VIII.4.1**: for any linear operator `P` on the actual
rational Schwartz space satisfying the named VIII.2.1, VIII.2.2, VIII.2.3 and translation laws,
`°e = P(1_H)` satisfies `IsRationalCuspidalUnit`. -/
theorem isRationalCuspidalUnit_of_degreeZeroLaws
    (hrange : RationalDegreeZeroRangeLaw hKc hPK ρ P)
    (htrans : RationalDegreeZeroTranslationLaw hKc hPK ρ P)
    (hconj : RationalDegreeZeroConjLaw hKc hPK ρ P)
    (hcheck : RationalDegreeZeroCheckLaw hKc hPK ρ P)
    (htwist : RationalDegreeZeroTwistLaw hKc hPK ρ P)
    (hconv : RationalDegreeZeroLeftConvolutionLaw hKc hPK ρ P μG) :
    IsRationalCuspidalUnit hKc hPK ρ μG H.toSubgroup
      (P (rationalSubgroupIndicator hKc hPK ρ μG H)) :=
  ⟨degreeZero_rationalSubgroupIndicator_mem_level hKc hPK ρ μG H hrange htrans,
    conj_degreeZero_rationalSubgroupIndicator hKc hPK ρ μG H hconj,
    degreeZero_rationalSubgroupIndicator_inv hKc hPK ρ μG H hcheck,
    fun _ hx => degreeZero_rationalSubgroupIndicator_support hKc hPK ρ μG H htwist hx,
    fun _ hφ x => convolution_degreeZero_rationalSubgroupIndicator hKc hPK ρ μG H hconv hφ x⟩

end Derivation

end Langlands.HarishChandraSchwartz
