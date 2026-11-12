import Langlands.Global.AdelicRationalHeightReductionStatement
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthStatement

/-! # Slice-wise growth gives full adelic growth under rational height reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

/-- A compact set meets only finitely many left cosets of an open subgroup. -/
theorem exists_finset_mem_leftCoset {X : Type*} [Group X] [TopologicalSpace X]
    [ContinuousMul X] (L : OpenSubgroup X) {Ω : Set X} (hΩ : IsCompact Ω) :
    ∃ B : Finset X, ∀ x ∈ Ω, ∃ b ∈ B, b⁻¹ * x ∈ L := by
  classical
  obtain ⟨B, hB⟩ := hΩ.elim_finite_subcover
    (fun b : Ω => (fun x => b.val⁻¹ * x) ⁻¹' (L : Set X))
    (fun _ => L.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  refine ⟨B.image Subtype.val, fun x hx => ?_⟩
  obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hB hx)
  exact ⟨b.val, Finset.mem_image_of_mem _ hb, hxb⟩

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- Actual continuous rational-invariant functions are invariant under the principal map. -/
theorem evaluate_rational_mul (f : ContinuousRationalFunctions F G)
    (q : RationalGroupPoints F G) (g : AdelicGroupPoints F G) :
    evaluate F G f (AdelicGroupPoints.rational F G q * g) = evaluate F G f g :=
  f.val.property q g

/-- A function fixed by an open finite subgroup takes on each left coset of that subgroup the
value of a fixed representative slice. -/
theorem evaluate_eq_infiniteSlice_of_mem (f : ContinuousRationalFunctions F G)
    {L : OpenSubgroup (FiniteAdelicGroupPoints F G)}
    (hL : ∀ l : L, finiteRightAction F G l f = f) (x : AdelicGroupPoints F G)
    {b : FiniteAdelicGroupPoints F G} (hb : b⁻¹ * AdelicGroupPoints.finite F G x ∈ L) :
    evaluate F G f x = infiniteSlice F G b f (AdelicGroupPoints.infinite F G x) := by
  have h := congrArg (fun f => evaluate F G f
    (AdelicGroupPoints.pair F G (AdelicGroupPoints.infinite F G x) b)) (hL ⟨_, hb⟩)
  change evaluate F G f (AdelicGroupPoints.pair F G (AdelicGroupPoints.infinite F G x) b *
      AdelicGroupPoints.ofFinite F G (b⁻¹ * AdelicGroupPoints.finite F G x)) =
    evaluate F G f (AdelicGroupPoints.pair F G (AdelicGroupPoints.infinite F G x) b) at h
  rw [AdelicGroupPoints.ofFinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one,
    mul_inv_cancel_left, AdelicGroupPoints.pair_projections] at h
  exact h

/-- Rational height reduction closes the slice-to-global moderate-growth comparison. -/
theorem adelicSliceModerateGrowthStatement_of_rationalHeightReduction
    (hred : RepresentationGrowth.AdelicRationalHeightReductionStatement.{u}) :
    AdelicSliceModerateGrowthStatement.{u} := by
  intro F _ _ G _ N rho hG hrho hN f hf hpoly
  obtain ⟨Ω, C, e, hΩ, hC, hreduce⟩ := hred F G rho hG hrho hN
  obtain ⟨L, hL⟩ := hf
  obtain ⟨B, hB⟩ := exists_finset_mem_leftCoset L hΩ
  choose K hK d hd using fun b : FiniteAdelicGroupPoints F G => hpoly b
  let D : ℕ := B.sup d
  let K₀ : ℝ := ∑ b ∈ B, K b
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg fun b _ => hK b
  apply (hasAdelicModerateGrowth_iff F G rho hN f).mpr
  refine ⟨K₀ * C ^ D, mul_nonneg hK₀ (pow_nonneg hC.le D), D * e, fun g => ?_⟩
  obtain ⟨q, hqΩ, hqh⟩ := hreduce g
  set x := AdelicGroupPoints.rational F G q * g with hx
  obtain ⟨b, hbB, hbL⟩ := hB _ hqΩ
  set a := AdelicGroupPoints.infinite F G x with ha
  have h1 : 1 ≤ RepresentationGrowth.height F G rho a :=
    RepresentationGrowth.one_le_height F G rho a
  have hH : 1 ≤ RepresentationGrowth.adelicHeight F G rho g :=
    RepresentationGrowth.one_le_adelicHeight F G rho hN g
  calc
    ‖evaluate F G f g‖ = ‖infiniteSlice F G b f a‖ := by
      rw [← evaluate_rational_mul F G f q g, ← hx]
      exact congrArg norm (evaluate_eq_infiniteSlice_of_mem F G f hL x hbL)
    _ ≤ K b * RepresentationGrowth.height F G rho a ^ d b := hd b a
    _ ≤ K₀ * RepresentationGrowth.height F G rho a ^ D := by
      apply mul_le_mul
      · exact Finset.single_le_sum (fun b _ => hK b) hbB
      · exact pow_le_pow_right₀ h1 (Finset.le_sup hbB)
      · exact pow_nonneg (zero_le_one.trans h1) _
      · exact hK₀
    _ ≤ K₀ * (C * RepresentationGrowth.adelicHeight F G rho g ^ e) ^ D := by
      apply mul_le_mul_of_nonneg_left _ hK₀
      exact pow_le_pow_left₀ (zero_le_one.trans h1) hqh D
    _ = (K₀ * C ^ D) * RepresentationGrowth.adelicHeight F G rho g ^ (D * e) := by
      rw [mul_pow, ← pow_mul, mul_comm e D]
      ring

end Langlands.Automorphic.GroupSchemeFunctions
