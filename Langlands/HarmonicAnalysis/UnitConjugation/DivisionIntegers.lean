import Langlands.HarmonicAnalysis.UnitConjugation.OrderLevels
import Langlands.Algebra.DivisionNormValuation
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Topology.Instances.Matrix
import Mathlib.RingTheory.Norm.Basic
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-!
# The integer ring of a division algebra over a local field

A finite-dimensional algebra over a nonarchimedean local field with its module topology has a
compact open order (`exists_isCompactOpenOrder`). For a finite-dimensional division algebra `D`,
the valuation of the regular norm `x ↦ valuation F (Algebra.norm F x)` is a valuation on `D`
(`divisionNormValuation`), and its integer ring (`divisionIntegers`) is a compact open order.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open ValuativeRel Filter _root_.Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section Order

variable {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A] [TopologicalSpace A]
  [IsModuleTopology F A]

variable (F A) in
/-- A finite-dimensional algebra over a nonarchimedean local field, with its module topology,
has a compact open subring stable under the integers of `F`. -/
theorem exists_isCompactOpenOrder : ∃ R : Subring A, IsCompactOpenOrder F R := by
  classical
  have := IsModuleTopology.isTopologicalRing F A
  let e := finiteDimensionalCoordinates F A
  have he : ∀ (c : F) (x : A), e (c • x) = c • e x := fun c x =>
    (Module.finBasis F A).equivFun.map_smul c x
  obtain ⟨s, hs⟩ := SelfDual.Internal.mem_some_box (Fin (Module.finrank F A)) (e 1)
  -- an `𝒪`-stable compact open subgroup containing `1`
  let B : AddSubgroup A := (SelfDual.Internal.boxSub (Fin (Module.finrank F A)) s).comap
    e.toAddEquiv.toAddMonoidHom
  have hmemB : ∀ x, x ∈ B ↔ e x ∈ SelfDual.Internal.box (Fin (Module.finrank F A)) s :=
    fun x => Iff.rfl
  have hBo : IsOpen (B : Set A) := (SelfDual.Internal.isOpen_box s).preimage e.continuous
  have hBc : IsCompact (B : Set A) := by
    have : (B : Set A) = e ⁻¹' SelfDual.Internal.box (Fin (Module.finrank F A)) s := rfl
    rw [this]
    exact e.toHomeomorph.isCompact_preimage.mpr (SelfDual.Internal.isCompact_box s)
  have hBcl : IsClosed (B : Set A) := B.isClosed_of_isOpen hBo
  have hB1 : (1 : A) ∈ B := hs
  have hBsmul : ∀ c : F, valuation F c ≤ 1 → ∀ x ∈ B, c • x ∈ B := by
    intro c hc x hx
    rw [hmemB, he]
    intro i _
    have hxi : valuation F (e x i) ≤ valuation F (s : F) := hx i trivial
    change valuation F (c * e x i) ≤ valuation F (s : F)
    rw [map_mul]
    exact (mul_le_of_le_one_left zero_le hc).trans hxi
  -- the left order of `B`
  let R : Subring A :=
    { carrier := {x | ∀ b ∈ B, x * b ∈ B}
      mul_mem' := fun {x y} hx hy b hb => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [mul_assoc]; exact hx _ (hy b hb)
      one_mem' := fun b hb => by simpa using hb
      add_mem' := fun {x y} hx hy b hb => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [add_mul]; exact B.add_mem (hx b hb) (hy b hb)
      zero_mem' := fun b _ => by simp [B.zero_mem]
      neg_mem' := fun {x} hx b hb => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [neg_mul]; exact B.neg_mem (hx b hb) }
  have hmemR : ∀ x, x ∈ R ↔ ∀ b ∈ B, x * b ∈ B := fun x => Iff.rfl
  refine ⟨R, ⟨?_, ?_, ?_⟩⟩
  · have hsub : (R : Set A) ⊆ B := fun x hx => by
      simpa using (hmemR x).mp hx 1 hB1
    have hcl : IsClosed (R : Set A) := by
      have : (R : Set A) = ⋂ b ∈ (B : Set A), (fun x => x * b) ⁻¹' (B : Set A) := by
        ext x; simp [hmemR]
      rw [this]
      exact isClosed_biInter fun b _ => hBcl.preimage (continuous_id.mul continuous_const)
    exact hBc.of_isClosed_subset hcl hsub
  · have hP : ∀ b ∈ (B : Set A), ∀ᶠ z : A × A in 𝓝 ((0 : A), b), z.1 * z.2 ∈ B := by
      intro b _
      have hcont : ContinuousAt (fun z : A × A => z.1 * z.2) ((0 : A), b) :=
        continuous_mul.continuousAt
      have : (B : Set A) ∈ 𝓝 ((fun z : A × A => z.1 * z.2) ((0 : A), b)) := by
        simpa using hBo.mem_nhds B.zero_mem
      exact hcont.preimage_mem_nhds this
    have hall := hBc.eventually_forall_of_forall_eventually
      (P := fun (x b : A) => x * b ∈ B) hP
    have hR0 : (R : Set A) ∈ 𝓝 (0 : A) := by
      filter_upwards [hall] with x hx using hx
    exact R.toAddSubgroup.isOpen_of_mem_nhds hR0
  · intro c hc x hx b hb
    rw [smul_mul_assoc]
    exact hBsmul c hc _ (hx b hb)

end Order

section Division

variable (D : Type*) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]

/-- The valuation of the regular norm is ultrametric on a finite-dimensional division algebra. -/
theorem valuation_regularNorm_add_le (x y : D) :
    valuation F (Algebra.norm F (x + y)) ≤
      max (valuation F (Algebra.norm F x)) (valuation F (Algebra.norm F y)) := by
  let := Langlands.LocalGalois.localNormedField F
  let := Langlands.LocalGalois.localNormedField_complete F
  let := Langlands.LocalGalois.localNormedField_ultrametric F
  have h := Langlands.CentralDivision.norm_regularNorm_add_le F D x y
  rw [le_max_iff] at h ⊢
  exact h.imp (Langlands.LocalGalois.localNormedField_le F _ _).mp
    (Langlands.LocalGalois.localNormedField_le F _ _).mp

/-- The valuation `x ↦ valuation F (Algebra.norm F x)` on a finite-dimensional division
algebra. -/
def divisionNormValuation : Valuation D (ValueGroupWithZero F) where
  toFun x := valuation F (Algebra.norm F x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp
  map_add_le_max' := valuation_regularNorm_add_le D

theorem divisionNormValuation_apply (x : D) :
    divisionNormValuation D x = valuation F (Algebra.norm F x) := rfl

/-- The integer ring `{x | valuation F (Algebra.norm F x) ≤ 1}` of a division algebra. -/
def divisionIntegers : Subring D := (divisionNormValuation (F := F) D).integer

theorem mem_divisionIntegers {x : D} :
    x ∈ divisionIntegers (F := F) D ↔ divisionNormValuation (F := F) D x ≤ 1 := Iff.rfl

theorem divisionNormValuation_algebraMap (c : F) :
    divisionNormValuation D (algebraMap F D c) = valuation F c ^ Module.finrank F D := by
  rw [divisionNormValuation_apply, Algebra.norm_algebraMap, map_pow]

theorem smul_mem_divisionIntegers {c : F} (hc : valuation F c ≤ 1) {x : D}
    (hx : x ∈ divisionIntegers (F := F) D) : c • x ∈ divisionIntegers (F := F) D := by
  rw [mem_divisionIntegers, Algebra.smul_def, map_mul, divisionNormValuation_algebraMap]
  exact mul_le_one' (pow_le_one₀ zero_le hc) hx

variable [TopologicalSpace D] [IsModuleTopology F D]

theorem continuous_regularNorm : Continuous fun x : D => Algebra.norm F x := by
  classical
  have := IsModuleTopology.toContinuousAdd F D
  let b := Module.finBasis F D
  have h : (fun x : D => Algebra.norm F x) =
      fun x => (LinearMap.toMatrix b b (Algebra.lmul F D x)).det := by
    funext x
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  rw [h]
  apply Continuous.matrix_det
  refine continuous_matrix fun i j => ?_
  let φ := (b.coord i).comp ((LinearMap.applyₗ' F (b j) : Module.End F D →ₗ[F] D).comp
    (Algebra.lmul F D).toLinearMap)
  have hφ : (fun x : D => LinearMap.toMatrix b b (Algebra.lmul F D x) i j) = φ := by
    funext x
    exact LinearMap.toMatrix_apply b b (Algebra.lmul F D x) i j
  rw [hφ]
  exact IsModuleTopology.continuous_of_linearMap φ

theorem isOpen_divisionIntegers : IsOpen (divisionIntegers (F := F) D : Set D) := by
  have hball : {z : F | valuation F z < 1} ∈ 𝓝 (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun z hz => hz⟩
  have hpre : (fun x : D => Algebra.norm F x) ⁻¹' {z : F | valuation F z < 1} ∈ 𝓝 (0 : D) := by
    apply (continuous_regularNorm D).continuousAt.preimage_mem_nhds
    simpa using hball
  have hO : (divisionIntegers (F := F) D : Set D) ∈ 𝓝 (0 : D) := by
    filter_upwards [hpre] with x hx
    exact le_of_lt (show valuation F (Algebra.norm F x) < 1 from hx)
  have := IsModuleTopology.isTopologicalRing F D
  exact (divisionIntegers (F := F) D).toAddSubgroup.isOpen_of_mem_nhds hO

theorem isCompact_divisionIntegers : IsCompact (divisionIntegers (F := F) D : Set D) := by
  classical
  have := Langlands.BruhatTits.localField_t2Space F
  have := IsModuleTopology.isTopologicalRing F D
  obtain ⟨R₀, hR₀⟩ := exists_isCompactOpenOrder F D
  obtain ⟨ϖ, hϖv, hϖ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  have hϖ : ϖ ≠ 0 := by simpa using hϖv
  -- the unit sphere of `R₀` and a lower bound for the norm on it
  let S : Set D := (R₀ : Set D) ∩ (orderLevel R₀ ϖ 1 : Set D)ᶜ
  have hS : IsCompact S := hR₀.isCompact.inter_right (isOpen_orderLevel hR₀ 1).isClosed_compl
  have hNS : IsCompact ((fun x : D => Algebra.norm F x) '' S) :=
    hS.image (continuous_regularNorm D)
  have h0 : (0 : F) ∉ (fun x : D => Algebra.norm F x) '' S := by
    rintro ⟨y, hy, hy0⟩
    have hy0' : y ≠ 0 := fun h => hy.2 (h ▸ (orderLevel R₀ ϖ 1).zero_mem)
    exact (Algebra.norm_ne_zero_iff.mpr hy0') hy0
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp
    (hNS.isClosed.isOpen_compl.mem_nhds h0)
  have hlow : ∀ y ∈ S, (γ : ValueGroupWithZero F) ≤ valuation F (Algebra.norm F y) := by
    intro y hy
    by_contra hlt
    push Not at hlt
    exact hγ hlt ⟨y, hy, rfl⟩
  obtain ⟨M, hM⟩ := exists_pow_lt₀ hϖ1 γ
  -- every integer lies in `ϖ ^ (-M) R₀`
  have hsub : (divisionIntegers (F := F) D : Set D) ⊆ (orderLevel R₀ ϖ (-(M : ℤ)) : Set D) := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact (orderLevel R₀ ϖ _).zero_mem
    let h := Nat.find (exists_mem_orderLevel_neg hR₀ hϖ1 x)
    have hxh : x ∈ orderLevel R₀ ϖ (-(h : ℤ)) :=
      Nat.find_spec (exists_mem_orderLevel_neg hR₀ hϖ1 x)
    by_cases hhM : h ≤ M
    · exact orderLevel_anti hϖ hR₀.smul_mem hϖ1 (by omega) hxh
    exfalso
    push Not at hhM
    have hmin : x ∉ orderLevel R₀ ϖ (-((h - 1 : ℕ) : ℤ)) :=
      Nat.find_min (exists_mem_orderLevel_neg hR₀ hϖ1 x) (by omega)
    set y : D := ϖ ^ (h : ℤ) • x with hy_def
    have hyS : y ∈ S := by
      refine ⟨?_, fun hy1 => hmin ?_⟩
      · have := (zpow_smul_mem_orderLevel_iff hϖ (h : ℤ) (-(h : ℤ)) x).mpr hxh
        rw [neg_add_cancel] at this
        exact mem_orderLevel_zero.mp this
      · have e1 : (1 : ℤ) = -((h - 1 : ℕ) : ℤ) + h := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ h)]; ring
        rw [e1] at hy1
        exact (zpow_smul_mem_orderLevel_iff hϖ (h : ℤ) _ x).mp hy1
    have hNy : Algebra.norm F y = ϖ ^ (h * Module.finrank F D) * Algebra.norm F x := by
      rw [hy_def, zpow_natCast, Algebra.smul_def, map_mul, Algebra.norm_algebraMap, ← pow_mul]
    have hv : valuation F (Algebra.norm F y) ≤ valuation F ϖ ^ (h * Module.finrank F D) := by
      rw [hNy, map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le hx
    have hn : 1 ≤ Module.finrank F D := Module.finrank_pos
    have hpow : valuation F ϖ ^ (h * Module.finrank F D) ≤ valuation F ϖ ^ M :=
      pow_le_pow_right_of_le_one' hϖ1.le (by nlinarith)
    exact absurd (hlow y hyS) (not_le.mpr ((hv.trans hpow).trans_lt hM))
  exact (isCompact_orderLevel hR₀ hϖ _).of_isClosed_subset
    ((divisionIntegers (F := F) D).toAddSubgroup.isClosed_of_isOpen (isOpen_divisionIntegers D))
    hsub

end Division

end Langlands.HarmonicAnalysis.UnitConjugation
