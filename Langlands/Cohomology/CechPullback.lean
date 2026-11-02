import Langlands.Cohomology.AbelianSheafH1Naturality

/-! # Ordered Čech cochains on preimage covers -/

noncomputable section

universe w u

open CategoryTheory Opposite TopologicalSpace

namespace Langlands.Cohomology.CechPullback

open Cech AbelianSheafCechH1

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (P : TopCat.Presheaf AddCommGrpCat.{u} X) {ι : Type w} (U : ι → Opens Y)

/-- Finite intersections in a preimage family are the preimages of the intersections. -/
lemma inter_preimage {n : ℕ} (σ : Fin n → ι) :
    inter (fun i => (Opens.map f).obj (U i)) σ = (Opens.map f).obj (inter U σ) := by
  apply Opens.ext
  simp only [inter, Opens.map_coe, Opens.coe_iInf, Set.preimage_iInter]

/-- Move cochains of a pushed-forward presheaf to the preimage open family. -/
def cochains (p : ℕ) :
    C ((Opens.map f).op ⋙ P) U p ≃+ C P (fun i => (Opens.map f).obj (U i)) p where
  toFun z σ := res (P := P) (inter_preimage f U σ).le (z σ)
  invFun z σ := res (P := P) (inter_preimage f U σ).ge (z σ)
  left_inv z := by
    funext σ
    change res (P := P) _ (res (P := P) _ (z σ)) = z σ
    rw [res_res, res_self]
  right_inv z := by
    funext σ
    change res (P := P) _ (res (P := P) _ (z σ)) = z σ
    rw [res_res, res_self]
  map_add' z z' := by
    funext σ
    exact map_add _ _ _

lemma cochains_apply (p : ℕ) (z : C ((Opens.map f).op ⋙ P) U p)
    (σ : Fin (p + 1) → ι) :
    cochains f P U p z σ = res (P := P) (inter_preimage f U σ).le (z σ) := rfl

/-- Cochain transport commutes with the ordered Čech differential. -/
lemma d_cochains (p : ℕ) (z : C ((Opens.map f).op ⋙ P) U p) :
    d P (fun i => (Opens.map f).obj (U i)) p (cochains f P U p z) =
      cochains f P U (p + 1) (d ((Opens.map f).op ⋙ P) U p z) := by
  funext τ
  rw [d_apply, cochains_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, cochains_apply]
  change _ • res (P := P) _ (res (P := P) _ _) =
    _ • res (P := P) _ (res (P := P)
      ((Opens.map f).map (homOfLE (inter_le_comp τ k.succAbove))).le _)
  rw [res_res, res_res]

/-- The inverse cochain transport also commutes with the differential. -/
lemma d_cochains_symm (p : ℕ) (z : C P (fun i => (Opens.map f).obj (U i)) p) :
    d ((Opens.map f).op ⋙ P) U p ((cochains f P U p).symm z) =
      (cochains f P U (p + 1)).symm (d P (fun i => (Opens.map f).obj (U i)) p z) := by
  apply (cochains f P U (p + 1)).injective
  rw [← d_cochains, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The induced additive equivalence of ordered one-cocycles. -/
def cocyclesEquiv :
    cocycles ((Opens.map f).op ⋙ P) U ≃+
      cocycles P (fun i => (Opens.map f).obj (U i)) where
  toFun z := ⟨cochains f P U 1 z.1, by
    change d P _ 1 (cochains f P U 1 z.1) = 0
    rw [d_cochains, show d _ _ 1 z.1 = 0 from z.2, map_zero]⟩
  invFun z := ⟨(cochains f P U 1).symm z.1, by
    change d _ _ 1 ((cochains f P U 1).symm z.1) = 0
    rw [d_cochains_symm, show d _ _ 1 z.1 = 0 from z.2, map_zero]⟩
  left_inv z := Subtype.ext ((cochains f P U 1).symm_apply_apply z.1)
  right_inv z := Subtype.ext ((cochains f P U 1).apply_symm_apply z.1)
  map_add' z z' := Subtype.ext ((cochains f P U 1).map_add z.1 z'.1)

/-- Moving a cocycle to the preimage family preserves, and reflects, coboundaries. -/
lemma cocyclesEquiv_mem_range (z : cocycles ((Opens.map f).op ⋙ P) U) :
    cocyclesEquiv f P U z ∈ (coboundaryHom P (fun i => (Opens.map f).obj (U i))).range ↔
      z ∈ (coboundaryHom ((Opens.map f).op ⋙ P) U).range := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(cochains f P U 0).symm a, ?_⟩
    apply (cocyclesEquiv f P U).injective
    apply Subtype.ext
    change cochains f P U 1 (d _ _ 0 ((cochains f P U 0).symm a)) = _
    rw [← d_cochains, AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val ha
  · rintro ⟨a, rfl⟩
    exact ⟨cochains f P U 0 a, Subtype.ext (d_cochains f P U 0 a)⟩

/-- Actual fixed-cover Čech H¹ is unchanged by moving a pushforward to the preimage family. -/
def h1Equiv : CechH1 ((Opens.map f).op ⋙ P) U ≃+
    CechH1 P (fun i => (Opens.map f).obj (U i)) :=
  QuotientAddGroup.congr _ _ (cocyclesEquiv f P U) (by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (cocyclesEquiv_mem_range f P U a).2 ha
    · intro hz
      refine ⟨(cocyclesEquiv f P U).symm z, ?_, AddEquiv.apply_symm_apply _ _⟩
      apply (cocyclesEquiv_mem_range f P U _).1
      simpa only [AddEquiv.apply_symm_apply] using hz)

lemma h1Equiv_mk (z : cocycles ((Opens.map f).op ⋙ P) U) :
    h1Equiv f P U (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (cocyclesEquiv f P U z) := rfl

end Langlands.Cohomology.CechPullback
