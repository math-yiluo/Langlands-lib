/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem tensorResolution_quasiIso_tensor_right
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {E E' K : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso α K (curriedTensor _))

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem tensorResolution_quasiIso_tensor_left
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {K L L' : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : L ⟶ L') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := curriedTensor (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)


/-- The category of module sheaves on the given ringed site. -/
abbrev tensorResolutionSiteModules {S : Type u} [Category.{u} S]
    {J : GrothendieckTopology S} (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

section
variable {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
variable (R : Sheaf J CommRingCat.{u})
local notation "C" => tensorResolutionSiteModules R
noncomputable local instance TensorResolutionComparison_localInst1 : MonoidalCategory C :=
  SheafOfModules.monoidalCategory R

/-- Comparison through a fixed K-flat resolution of the second argument. -/
noncomputable def tensorResolutionComparison
    (E K M F N : CochainComplex C ℤ)
    (r : E ⟶ M) (q : K ⟶ M) (s : F ⟶ N)
    (hE : E.IsKFlatTensor) (hK : K.IsKFlatTensor) (hF : F.IsKFlatTensor)
    (hr : QuasiIso r) (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (CochainComplex.mapBifunctor E N (curriedTensor C)).homology i ≅
      (CochainComplex.mapBifunctor K N (curriedTensor C)).homology i := by
  let a := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor C) (.up ℤ)
  let b := HomologicalComplex.mapBifunctorMap r (𝟙 F) (curriedTensor C) (.up ℤ)
  let c := HomologicalComplex.mapBifunctorMap q (𝟙 F) (curriedTensor C) (.up ℤ)
  let d := HomologicalComplex.mapBifunctorMap (𝟙 K) s (curriedTensor C) (.up ℤ)
  have : QuasiIso a := tensorResolution_quasiIso_tensor_left s hs hE
  have : QuasiIso b := tensorResolution_quasiIso_tensor_right r hr hF
  have : QuasiIso c := tensorResolution_quasiIso_tensor_right q hq hF
  have : QuasiIso d := tensorResolution_quasiIso_tensor_left s hs hK
  exact (asIso (HomologicalComplex.homologyMap a i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap b i) ≪≫
    (asIso (HomologicalComplex.homologyMap c i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap d i)

attribute [irreducible] tensorResolutionComparison

end

/-- Four commuting squares remain commuting when the two backward arrows are inverted. -/
theorem tensorResolution_zigzag_naturality
    {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : C}
    (a₀ : A₁ ⟶ A₀) (a₁ : A₁ ⟶ A₂) (a₂ : A₃ ⟶ A₂) (a₃ : A₃ ⟶ A₄)
    (b₀ : B₁ ⟶ B₀) (b₁ : B₁ ⟶ B₂) (b₂ : B₃ ⟶ B₂) (b₃ : B₃ ⟶ B₄)
    [IsIso a₀] [IsIso a₂] [IsIso b₀] [IsIso b₂]
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (f₃ : A₃ ⟶ B₃) (f₄ : A₄ ⟶ B₄)
    (h₀ : a₀ ≫ f₀ = f₁ ≫ b₀) (h₁ : a₁ ≫ f₂ = f₁ ≫ b₁)
    (h₂ : a₂ ≫ f₂ = f₃ ≫ b₂) (h₃ : a₃ ≫ f₄ = f₃ ≫ b₃) :
    (inv a₀ ≫ a₁ ≫ inv a₂ ≫ a₃) ≫ f₄ =
      f₀ ≫ (inv b₀ ≫ b₁ ≫ inv b₂ ≫ b₃) := by
  have h₂' : inv a₂ ≫ f₃ = f₂ ≫ inv b₂ := by
    apply (cancel_epi a₂).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [reassoc_of% h₂]
    simp
  apply (cancel_epi a₀).1
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [reassoc_of% h₀, IsIso.hom_inv_id_assoc, ← reassoc_of% h₁,
    h₃, reassoc_of% h₂']

end AlgebraicGeometry
