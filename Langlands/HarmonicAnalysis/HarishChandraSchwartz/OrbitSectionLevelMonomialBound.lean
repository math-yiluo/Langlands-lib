import Langlands.HarmonicAnalysis.TorusMonomialMixedDerivativeBound

/-! # Finite level bounds for smooth coefficients after monomial change -/

noncomputable section

open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ uJ' uB

private theorem length_le_of_mem_torusDerivativeLists
    {J : Type uJ} [Fintype J] [DecidableEq J] {n : ℕ} {l : List J}
    (hl : l ∈ torusDerivativeLists n) : l.length ≤ n := by
  induction n generalizing l with
  | zero =>
    have : l = [] := by simpa [torusDerivativeLists] using hl
    simp [this]
  | succ n ih =>
    rw [torusDerivativeLists, Finset.mem_union] at hl
    rcases hl with hl | hl
    · have : l = [] := Finset.mem_singleton.mp hl
      simp [this]
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hl
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hj
      exact Nat.succ_le_succ (ih hm)

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] [DecidableEq J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (H : OpenSubgroup G)

set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture h K π.obj
set_option hygiene false in
local notation "Level" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "seminorms" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "coeff" => orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK

/-- A smooth scalar coefficient given by a finite sum of weighted input
coordinates followed by a monomial pullback has each output seminorm bounded
by a finite supremum of original level seminorms. -/
theorem exists_orbitSectionLevel_monomialSeminorm_bound
    {J' : Type uJ'} [Fintype J'] [DecidableEq J'] (a : J → J' → ℤ)
    {B : Type uB} (S : Finset B) (w : B → smoothFiniteTorusFunctions J)
    (d : B → Module.Dual ℂ Picture) (F : Level → smoothFiniteTorusFunctions J')
    (hF : ∀ q z, (F q).val z = ∑ b ∈ S,
      (w b).val (finiteTorusMonomial a z) * (coeff (d b) (includeLevel q)).val (finiteTorusMonomial a z))
    (l : List J') :
    ∃ t : Finset (List J × Module.Dual ℂ Picture), ∃ c : ℝ≥0,
      ∀ q : Level, smoothTorusSeminorm J' l (F q) ≤ (c : ℝ) * (t.sup seminorms) q := by
  classical
  let n := l.length
  let t : Finset (List J × Module.Dual ℂ Picture) :=
    S.biUnion fun b => (torusDerivativeLists (J := J) n).image fun m => (m, d b)
  let C (b : B) := (2 : ℝ) ^ n * smoothTorusDerivativeControl n (w b)
  have hC (b : B) : 0 ≤ C b := mul_nonneg (by positivity) (apply_nonneg _ _)
  let A := (l.map fun k => ∑ j, ‖(a j k : ℂ)‖).prod
  have hA : 0 ≤ A := by
    apply List.prod_nonneg
    intro r hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨t, ⟨A * ∑ b ∈ S, C b, mul_nonneg hA (Finset.sum_nonneg fun b _ => hC b)⟩, fun q => ?_⟩
  let f (b : B) := coeff (d b) (includeLevel q)
  let g := ∑ b ∈ S, w b * f b
  have hFg : F q = smoothTorusMonomialPullback a g := by
    apply Subtype.ext
    funext z
    rw [hF q z, smoothTorusMonomialPullback_apply]
    simp [g, f]
  have hcontrol (b : B) (hb : b ∈ S) : smoothTorusDerivativeControl n (f b) ≤ (t.sup seminorms) q := by
    unfold smoothTorusDerivativeControl
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro m hm
    have hmem : (m, d b) ∈ t := Finset.mem_biUnion.mpr
      ⟨b, hb, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    exact (Finset.le_sup (f := seminorms) hmem) q
  have hg : smoothTorusDerivativeControl n g ≤ (∑ b ∈ S, C b) * (t.sup seminorms) q := by
    unfold smoothTorusDerivativeControl at ⊢
    apply Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun b _ => hC b) (apply_nonneg _ _))
    intro m hm
    have hm' := length_le_of_mem_torusDerivativeLists hm
    change smoothTorusSeminorm J m (∑ b ∈ S, w b * f b) ≤ _
    rw [smoothTorusSeminorm_apply, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ S, ‖smoothTorusDerivative J m (w b * f b)‖
        ≤ ∑ b ∈ S, C b * (t.sup seminorms) q := by
          refine Finset.sum_le_sum fun b hb => ?_
          change smoothTorusSeminorm J m (w b * f b) ≤ _
          apply (smoothTorusSeminorm_le_iff J m _ (mul_nonneg (hC b) (apply_nonneg _ _))).mpr
          intro z
          exact (norm_torusPartialDerivList_mul_le_control n (w b) (f b) m hm' z).trans
            (mul_le_mul_of_nonneg_left (hcontrol b hb) (hC b))
      _ = _ := by rw [← Finset.sum_mul]
  rw [hFg]
  exact (smoothTorusSeminorm_monomialPullback_le a l g).trans <| by
    change A * smoothTorusDerivativeControl n g ≤ (A * ∑ b ∈ S, C b) * (t.sup seminorms) q
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hg hA

end Langlands.HarishChandraSchwartz
