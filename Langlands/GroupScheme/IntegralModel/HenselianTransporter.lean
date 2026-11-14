import Langlands.GroupScheme.Torus.HenselianNormalizerLifting

/-! # Exact integral transporters and their generic conjugacy equation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {H : GroupScheme (Spec (CommRingCat.of R))}

/-- An integral section transporting two specified homomorphisms and recovering
the specified point over the auxiliary field. -/
structure TransporterData {k : Type u} [Field k] [Algebra R k]
    (j₁ j₂ : H ⟶ M.group)
    (g₀ : Over.mk (Spec.algebraMap R k) ⟶ M.group.X) where
  section_ : M.integralSections
  isTransporter : PointwiseSchemeAction.IsTransporter j₁ j₂ section_
  residue_eq :
    (Over.homMk (Spec.algebraMap R k) (by simp) :
      Over.mk (Spec.algebraMap R k) ⟶ Over.mk (𝟙 _)) ≫ section_ = g₀

/-- The actual generic point of an integral transporter, using the model's
specified generic-fibre identification. -/
def TransporterData.genericPoint {k : Type u} [Field k] [Algebra R k]
    {j₁ j₂ : H ⟶ M.group}
    {g₀ : Over.mk (Spec.algebraMap R k) ⟶ M.group.X}
    (A : M.TransporterData j₁ j₂ g₀) : rationalPoints G :=
  M.integralPointMap A.section_

theorem TransporterData.genericPoint_mem_integralPoints
    {k : Type u} [Field k] [Algebra R k]
    {j₁ j₂ : H ⟶ M.group}
    {g₀ : Over.mk (Spec.algebraMap R k) ⟶ M.group.X}
    (A : M.TransporterData j₁ j₂ g₀) :
    A.genericPoint ∈ M.integralPoints :=
  ⟨A.section_, rfl⟩

/-- An integral all-test transporter conjugates the second generic map to
the first, through the model's actual integral-point map. -/
theorem genericHom_comp_innerIso_of_isTransporter
    (j₁ j₂ : H ⟶ M.group) (g : M.integralSections)
    (hg : PointwiseSchemeAction.IsTransporter j₁ j₂ g) :
    M.genericHom j₂ ≫ (G.innerIso (M.integralPointMap g)).hom =
      M.genericHom j₁ := by
  have h := (hg.baseChange (Spec.algebraMap R K)
    (Over.homMk (Spec.algebraMap R K) (by simp) :
      (Over.map (Spec.algebraMap R K)).obj (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _))
    (baseChangeSectionHom (Spec.algebraMap R K) M.group g)
    (baseChangePointsEquiv_baseChangeSectionHom (Spec.algebraMap R K) M.group g)).map
      M.genericIso.hom
  change PointwiseSchemeAction.IsTransporter (M.genericHom j₁)
    (M.genericHom j₂) (M.integralPointMap g) at h
  apply hom_ext_points
  intro V x
  rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom]
  have hx := h V (Over.homMk V.hom (by simp)) x
  change (x ≫ (M.genericHom j₁).hom.hom) *
      G.constantPoint (M.integralPointMap g) V =
    G.constantPoint (M.integralPointMap g) V *
      (x ≫ (M.genericHom j₂).hom.hom) at hx
  rw [← hx, mul_inv_cancel_right]

/-- The generic conjugation equation of the specified transporter data. -/
theorem TransporterData.generic_comm {k : Type u} [Field k] [Algebra R k]
    {j₁ j₂ : H ⟶ M.group}
    {g₀ : Over.mk (Spec.algebraMap R k) ⟶ M.group.X}
    (A : M.TransporterData j₁ j₂ g₀) :
    M.genericHom j₂ ≫ (G.innerIso A.genericPoint).hom = M.genericHom j₁ :=
  M.genericHom_comp_innerIso_of_isTransporter j₁ j₂ A.section_ A.isTransporter

variable [HenselianLocalRing R]
  {k : Type u} [Field k] [Algebra R k]

/-- Choose an actual integral transporter with exact recovery of a prescribed
residue transporter between two maps from the same split torus. -/
def henselianTransporter (j₁ j₂ : H ⟶ M.group) (hH : IsSplitTorus H)
    (hM : M.IsSmooth) (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (Spec.algebraMap R k) ⟶ M.group.X)
    (hg₀ : PointwiseSchemeAction.IsTransporter j₁ j₂ g₀) :
    M.TransporterData j₁ j₂ g₀ := by
  classical
  letI : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  let h := PointwiseSchemeAction.exists_henselian_transporter_of_split
    j₁ j₂ hH hM hk g₀ hg₀
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

end Langlands.GroupScheme.IntegralModel
