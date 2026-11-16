import Langlands.Global.RankinSelberg.DualExpansionRectMeasure

/-! # The unfolded rectangular side as a sum of rectangle integrals -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (IsPeriodic ratVec ratVec_apply)

variable {F : Type u} [Field F] [NumberField F]

local instance dualUnfoldSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualUnfoldSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance dualUnfoldAdelesLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F
local instance dualUnfoldRectMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _
local instance dualUnfoldRectBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

variable {m K : ℕ}

section Lattice

/-- A rational rectangle as an adelic matrix. -/
def ratMat (B : Fin K × Fin m → F) : Matrix (Fin K) (Fin m) (Adeles F) :=
  fun i j => algebraMap F (Adeles F) (B (i, j))

theorem ratMat_mem (B : Fin K × Fin m → F) : ratMat B ∈ rectLattice F K m :=
  ⟨fun i j => B (i, j), rfl⟩

theorem ratMat_injective : Function.Injective (ratMat (F := F) (m := m) (K := K)) := by
  intro B B' h
  funext p
  exact AdeleRing.algebraMap_injective (𝓞 F) F (congrFun (congrFun h p.1) p.2)

/-- The rational rectangles, indexed by `F^{K×m}`. -/
def latticeEquiv : (Fin K × Fin m → F) ≃ rectLattice F K m :=
  Equiv.ofBijective (fun B => ⟨ratMat B, ratMat_mem B⟩)
    ⟨fun B B' h => ratMat_injective (congrArg Subtype.val h), fun c => by
      obtain ⟨C, hC⟩ := c.property
      refine ⟨fun p => C p.1 p.2, Subtype.ext ?_⟩
      rw [← hC]
      rfl⟩

theorem coe_latticeEquiv (B : Fin K × Fin m → F) :
    ((latticeEquiv B : rectLattice F K m) : Matrix (Fin K) (Fin m) (Adeles F)) = ratMat B := rfl

end Lattice

section Integrand

/-- The rectangle integrand `v ↦ W(diag(p, I) x̂_v y)`. -/
def rectIntegrand (K : ℕ) (W : Points F (m + K + 1) → ℂ) (y : Points F (m + K + 1))
    (p : UnipotentRationalCosets F m) (v : Matrix (Fin K) (Fin m) (Adeles F)) : ℂ :=
  W (padRational F (show m ≤ m + K + 1 by omega) p.out *
    xcPoint F (fun q => v q.1 q.2) 0 * y)

theorem rectIntegrand_ratMat_add (W : Points F (m + K + 1) → ℂ) (y : Points F (m + K + 1))
    (p : UnipotentRationalCosets F m) (B : Fin K × Fin m → F)
    (v : Matrix (Fin K) (Fin m) (Adeles F)) :
    rectIntegrand K W y p (ratMat B + v) = rectFamily K W y (fun q => v q.1 q.2) (p, B) := by
  unfold rectIntegrand rectFamily
  have : (fun q : Fin K × Fin m => (ratMat B + v) q.1 q.2) =
      (fun q => v q.1 q.2) + fun q => algebraMap F (Adeles F) ((p, B).2 q) := by
    funext q
    simp only [Matrix.add_apply, ratMat, Pi.add_apply]
    rw [add_comm]
  rw [this]

end Integrand

section Sums

variable [CompactSpace (AdeleQuotient F)] {ψ : AddChar (Adeles F) ℂ}
  (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) {W : Points F (m + K + 1) → ℂ}
include hψF

omit [CompactSpace (AdeleQuotient F)] hψF in
theorem DualData.continuous_rectIntegrand' (hW : DualData F m ψ K W) (y : Points F (m + K + 1))
    (p : UnipotentRationalCosets F m) : Continuous (rectIntegrand K W y p) := by
  have h1 : Continuous fun v : Matrix (Fin K) (Fin m) (Adeles F) =>
      xcPoint F (m := m) (fun q => v q.1 q.2) 0 :=
    (continuous_xcPoint_left 0).comp
      (continuous_pi fun q => (continuous_apply q.2).comp (continuous_apply q.1))
  exact hW.continuous.comp ((continuous_const.mul h1).mul continuous_const)

omit [CompactSpace (AdeleQuotient F)] in
/-- The family over the rectangle coordinates for a fixed coset. -/
theorem DualData.locUnifSummable_rectFamily_fixed (hW : DualData F m ψ K W)
    (y : Points F (m + K + 1)) (p : UnipotentRationalCosets F m) :
    LocUnifSummable (fun (B : Fin K × Fin m → F) (X : Fin K × Fin m → Adeles F) =>
      rectFamily K W y X (p, B)) :=
  (hW.locUnifSummable_rectFamily hψF y).comp_injective (fun _ _ h => congrArg Prod.snd h)

omit [CompactSpace (AdeleQuotient F)] in
theorem DualData.continuous_tsum_rectFamily_fixed (hW : DualData F m ψ K W)
    (y : Points F (m + K + 1)) (p : UnipotentRationalCosets F m) :
    Continuous fun X : Fin K × Fin m → Adeles F => ∑' B, rectFamily K W y X (p, B) := by
  refine (hW.locUnifSummable_rectFamily_fixed hψF y p).continuous_tsum fun B => ?_
  have h1 : Continuous fun X : Fin K × Fin m → Adeles F =>
      xcPoint F (m := m) (X + fun q => algebraMap F (Adeles F) (B q)) 0 :=
    (continuous_xcPoint_left 0).comp (continuous_id.add continuous_const)
  exact hW.continuous.comp ((continuous_const.mul h1).mul continuous_const)

omit [CompactSpace (AdeleQuotient F)] hψF in
theorem isPeriodic_tsum_rectFamily_fixed (y : Points F (m + K + 1))
    (p : UnipotentRationalCosets F m) :
    IsPeriodic fun X : Fin K × Fin m → Adeles F => ∑' B, rectFamily K W y X (p, B) := by
  intro X ρ
  show ∑' B, rectFamily K W y (X + ratVec ρ) (p, B) = ∑' B, rectFamily K W y X (p, B)
  have h : ∀ B, rectFamily K W y (X + ratVec ρ) (p, B) =
      rectFamily K W y X (p, Equiv.addLeft ρ B) := by
    intro B
    unfold rectFamily
    have e : (X + ratVec ρ + fun q => algebraMap F (Adeles F) ((p, B).2 q)) =
        X + fun q => algebraMap F (Adeles F) ((p, Equiv.addLeft ρ B).2 q) := by
      funext q
      simp [ratVec, add_assoc]
    rw [e]
  rw [tsum_congr h]
  exact (Equiv.addLeft ρ).tsum_eq (fun B => rectFamily K W y X (p, B))

/-- **One rectangle integral** of the unfolded side: integrability, and the value as a torus
integral of the sum over the rational rectangles. -/
theorem DualData.integral_rectIntegrand (hW : DualData F m ψ K W) (y : Points F (m + K + 1))
    (p : UnipotentRationalCosets F m) :
    Integrable (rectIntegrand K W y p) (rectangleMeasure F K m) ∧
      ∫ v, rectIntegrand K W y p v ∂rectangleMeasure F K m =
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
          (fun X => ∑' B, rectFamily K W y X (p, B)) := by
  obtain ⟨C, hC⟩ := hW.exists_rectFamily_bound hψF y
  have hfam : ∀ v : Matrix (Fin K) (Fin m) (Adeles F), (fun c : rectLattice F K m =>
      rectIntegrand K W y p (c + v)) ∘ latticeEquiv =
        fun B => rectFamily K W y (fun q => v q.1 q.2) (p, B) := by
    intro v
    funext B
    simp only [Function.comp_apply, coe_latticeEquiv]
    exact rectIntegrand_ratMat_add W y p B v
  have hsumB : ∀ X : Fin K × Fin m → Adeles F,
      Summable fun B => ‖rectFamily K W y X (p, B)‖ :=
    fun X => (hW.locUnifSummable_rectFamily_fixed hψF y p).1 X
  have hboundB : ∀ X : Fin K × Fin m → Adeles F,
      ∑' B, ‖rectFamily K W y X (p, B)‖ ≤ C := by
    intro X
    refine le_trans ?_ (hC X)
    exact tsum_comp_le_tsum_of_inj ((hW.locUnifSummable_rectFamily hψF y).1 X)
      (fun _ => norm_nonneg _) (fun B B' h => congrArg Prod.snd h)
  have hint : Integrable (rectIntegrand K W y p) (rectangleMeasure F K m) := by
    refine integrable_of_tsum_norm_le F K m _ (hW.continuous_rectIntegrand' y p)
      (C := C) (fun v => ?_) (fun v => ?_)
    · rw [← latticeEquiv.summable_iff]
      have := hsumB (fun q => v q.1 q.2)
      convert this using 1
      funext B
      simp only [Function.comp_apply, coe_latticeEquiv, rectIntegrand_ratMat_add]
    · rw [← latticeEquiv.tsum_eq]
      have := hboundB (fun q => v q.1 q.2)
      convert this using 2
      funext B
      simp only [coe_latticeEquiv, rectIntegrand_ratMat_add]
  refine ⟨hint, integral_rectangleMeasure_eq_torusIntegral F K m _ hint _
    (isPeriodic_tsum_rectFamily_fixed y p) (hW.continuous_tsum_rectFamily_fixed hψF y p)
    fun v => ?_⟩
  rw [← latticeEquiv.hasSum_iff, hfam v]
  exact (hsumB _).of_norm.hasSum

/-- **The unfolded side as a sum of rectangle integrals**:
`dualRectT K W y = Σ_{p ∈ N_m(F) \ GL_m(F)} ∫_{M_{K×m}(𝔸)} W(diag(p, I) x̂_v y) dv`, with absolute
convergence. -/
theorem DualData.hasSum_integral_rectIntegrand (hW : DualData F m ψ K W)
    (y : Points F (m + K + 1)) :
    HasSum (fun p => ∫ v, rectIntegrand K W y p v ∂rectangleMeasure F K m) (dualRectT K W y) := by
  obtain ⟨C, hC⟩ := hW.exists_rectFamily_bound hψF y
  have hval : ∀ p, ∫ v, rectIntegrand K W y p v ∂rectangleMeasure F K m =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
        (fun X => ∑' B, rectFamily K W y X (p, B)) :=
    fun p => (hW.integral_rectIntegrand hψF y p).2
  simp_rw [hval]
  have hnorm : ∀ X : Fin K × Fin m → Adeles F,
      Summable fun pB => ‖rectFamily K W y X pB‖ :=
    fun X => (hW.locUnifSummable_rectFamily hψF y).1 X
  have hterm : ∀ (X : Fin K × Fin m → Adeles F) (p : UnipotentRationalCosets F m),
      ‖∑' B, rectFamily K W y X (p, B)‖ ≤ ∑' B, ‖rectFamily K W y X (p, B)‖ :=
    fun X p => norm_tsum_le_tsum_norm ((hnorm X).prod_factor p)
  have hsumG : ∀ X : Fin K × Fin m → Adeles F,
      Summable fun p : UnipotentRationalCosets F m => ∑' B, ‖rectFamily K W y X (p, B)‖ :=
    fun X => (hnorm X).prod
  have hGle : ∀ X : Fin K × Fin m → Adeles F,
      ∑' p : UnipotentRationalCosets F m, ∑' B, ‖rectFamily K W y X (p, B)‖ ≤ C := by
    intro X
    rw [← (hnorm X).tsum_prod' (fun p => (hnorm X).prod_factor p)]
    exact hC X
  have hs : ∀ X : Fin K × Fin m → Adeles F, Summable fun p : UnipotentRationalCosets F m =>
      ‖∑' B, rectFamily K W y X (p, B)‖ :=
    fun X => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm X) (hsumG X)
  have hB : ∀ X : Fin K × Fin m → Adeles F, ∑' p : UnipotentRationalCosets F m,
      ‖∑' B, rectFamily K W y X (p, B)‖ ≤ C :=
    fun X => (Summable.tsum_le_tsum (hterm X) (hs X) (hsumG X)).trans (hGle X)
  have htsum : ∑' p, Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
      (fun X => ∑' B, rectFamily K W y X (p, B)) = dualRectT K W y := by
    rw [← torusIntegral_tsum (fun p => hW.continuous_tsum_rectFamily_fixed hψF y p)
      (fun p => isPeriodic_tsum_rectFamily_fixed y p) hs hB]
    unfold dualRectT
    refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun X => ?_
    exact ((hnorm X).of_norm.tsum_prod' (fun p => (hnorm X).of_norm.prod_factor p)).symm
  have hfin : ∀ s : Finset (UnipotentRationalCosets F m), ∑ p ∈ s,
      ‖Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
        (fun X => ∑' B, rectFamily K W y X (p, B))‖ ≤ C :=
    sum_norm_torusIntegral_le (fun p => hW.continuous_tsum_rectFamily_fixed hψF y p)
      (fun p => isPeriodic_tsum_rectFamily_fixed y p) hs hB
  have hsumm := (summable_of_sum_le (fun _ => norm_nonneg _) hfin).of_norm
  rw [← htsum]
  exact hsumm.hasSum

end Sums

end Langlands.Global.RankinSelbergGlobal.Unfolding
