import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelFiberGenerators

/-! # Finite level seminorms for bounds on compact fibers -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ uB

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] [DecidableEq J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (H : OpenSubgroup G) (hHK : H ≤ K)

set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture h K π.obj
set_option hygiene false in
local notation "Level" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "Fixed" => orbitSectionFixedCoefficients h K π H
set_option hygiene false in
local notation "fixedRestriction" => orbitSectionLevelFixedRestriction h K π ν e hU hP hK hν hr hPK H hHK
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "seminorms" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK H

/-- A common bound on a finite basis of the fixed compact fiber gives a finite
zero-order seminorm bound for the entire section level. The evaluation domain
can be any set, including a proper-parabolic region. -/
theorem exists_levelFamily_bound_of_fixedBasis {B : Type uB} [Fintype B]
    (b : Module.Basis B ℂ Fixed) {X : Type*} (U₀ : Set X) (W : X → ℝ)
    (L : (J → Circle) → X → (Fixed →ₗ[ℂ] ℂ)) (D : ℝ≥0)
    (hL : ∀ i z x, x ∈ U₀ → ‖L z x (b i)‖ ≤ (D : ℝ) * W x) :
    ∃ t : Finset (List J × Module.Dual ℂ Picture), ∃ C : ℝ≥0,
      ∀ (q : Level) (z : J → Circle) (x : X), x ∈ U₀ →
        ‖L z x (fixedRestriction q z)‖ ≤ (C : ℝ) * (t.sup seminorms) q * W x := by
  classical
  choose ℓ hℓ using fun i : B => (b.coord i).exists_extend
  let t : Finset (List J × Module.Dual ℂ Picture) := Finset.univ.image fun i => ([], ℓ i)
  refine ⟨t, (Fintype.card B : ℝ≥0) * D, fun q z x hx => ?_⟩
  let v := fixedRestriction q z
  have hcoordinate (i : B) : ‖b.coord i v‖ ≤ (t.sup seminorms) q := by
    have he : ℓ i v.val = b.coord i v := LinearMap.congr_fun (hℓ i) v
    have hb := norm_torusPartialDerivList_le_orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK
      [] (ℓ i) (includeLevel q) z
    change ‖ℓ i v.val‖ ≤ seminorms ([], ℓ i) q at hb
    rw [he] at hb
    have hmem : ([], ℓ i) ∈ t := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact hb.trans ((Finset.le_sup (f := seminorms) hmem) q)
  have hsum : ∑ i, b.coord i v * L z x (b i) = L z x v := by
    have he := congrArg (L z x) (b.sum_repr v)
    simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply] using he
  change ‖L z x v‖ ≤ _
  rw [← hsum]
  calc ‖∑ i, b.coord i v * L z x (b i)‖ ≤ ∑ i, ‖b.coord i v * L z x (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : B, (t.sup seminorms) q * ((D : ℝ) * W x) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (hcoordinate i) (hL i z x hx) (norm_nonneg _) (apply_nonneg _ _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast]; ring

end Langlands.HarishChandraSchwartz
