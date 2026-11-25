/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison

/-! # Module adjunction for an independently sized inverse image
Source: Stacks Project, Modules on Sites, Tags 03D3 and 03D7.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.CochainInversePairing
open CochainGeometricConstruction GeometricConstruction CochainScalarConstruction
attribute [local irreducible] monoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private noncomputable def restrictHomEquiv
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) :
    (X₁ ⟶ X₂) ≃ (Y₁ ⟶ Y₂) where
  toFun f := Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩)
  invFun g := Classical.choose ((h (E.symm (G.map g))).mpr
    ⟨g, (E.apply_symm_apply _).symm⟩)
  left_inv f := by
    apply F.map_injective
    have hf := Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)
    have hg := Classical.choose_spec ((h (E.symm (G.map
      (Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩))))).mpr
        ⟨_, (E.apply_symm_apply _).symm⟩)
    rw [hg, hf, E.symm_apply_apply]
  right_inv g := by
    apply G.map_injective
    have hg := Classical.choose_spec ((h (E.symm (G.map g))).mpr
      ⟨g, (E.apply_symm_apply _).symm⟩)
    have hf := Classical.choose_spec ((h (F.map (Classical.choose
      ((h (E.symm (G.map g))).mpr ⟨g, (E.apply_symm_apply _).symm⟩)))).mp ⟨_, rfl⟩)
    rw [hf, hg, E.apply_symm_apply]

private theorem restrictHomEquiv_map
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) (f : X₁ ⟶ X₂) :
    G.map (restrictHomEquiv F G E h f) = E (F.map f) :=
  Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)


/-- The specified algebraic inverse image has a module right adjoint.
Source: Stacks Project, Modules on Sites, Tags 03D3 and 03D7.
(auxiliary; not a blueprint node).

Proof: transport modules along the product-preserving right adjoint, with the
coefficient action induced by the adjunct of the ring comparison. The graph equations
for addition and scalar multiplication identify linear maps with the linear maps
among their set-sheaf adjuncts. Restrict that bijection, whose inverse equations
hold by faithfulness. Naturality follows from that of the set adjunction and the
specified underlying comparisons. The natural Hom bijection gives the adjunction. -/
theorem inverseImageModuleAdjunction_exists
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : F ⊣ V) [PreservesFiniteLimits F]
    (I : AlgebraicInverseImage F R RI) :
    ∃ P : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RI) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      Nonempty (I.modules ⊣ P) := by
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  let : V.Braided := Functor.Braided.ofChosenFiniteProducts V
  have hR := ringOperations R RI F I
  obtain ⟨P, eP, hOps⟩ := right_module_construction F V adj R RI I.ringUnderlying.symm
    ((binary_transport_iff F _ _ I.ringUnderlying.symm _ _).1 hR.1)
    ((binary_transport_iff F _ _ I.ringUnderlying.symm _ _).1 hR.2)
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  let E := fun M0 H0 ↦ mateIsoEquiv adj (eI.app M0) (eP.app H0)
  have hE : E = fun M0 H0 ↦ mateIsoEquiv adj (eI.app M0) (eP.app H0) := rfl
  have hImage M0 H0 (α : (CochainScalarConstruction.underlying RI).obj (I.modules.obj M0) ⟶
      (CochainScalarConstruction.underlying RI).obj H0) :
      (∃ a : I.modules.obj M0 ⟶ H0, (CochainScalarConstruction.underlying RI).map a = α) ↔
        ∃ b : M0 ⟶ P.obj H0, (CochainScalarConstruction.underlying R).map b = E M0 H0 α := by
    set_option backward.isDefEq.respectTransparency false in
    have hLA : F.map (madd R M0) =
        prodComparison F ((CochainScalarConstruction.underlying R).obj M0)
          ((CochainScalarConstruction.underlying R).obj M0) ≫
          prod.map (eI.inv.app M0) (eI.inv.app M0) ≫
            madd RI (I.modules.obj M0) ≫ eI.hom.app M0 := by
      apply (cancel_mono (eI.inv.app M0)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph F (eI.inv.app M0) (eI.inv.app M0) (eI.inv.app M0)
        (madd R M0) (madd RI (I.modules.obj M0))
        (fun U x y ↦ @Add.add (M0.val.obj U) inferInstance x y)
        (fun U x y ↦ @Add.add ((I.modules.obj M0).val.obj U) inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T x y z hz U t ↦ I.moduleAdd M0 T x y z hz U t)
    set_option backward.isDefEq.respectTransparency false in
    have hLS : F.map (msmul R M0) =
        prodComparison F (rset R) ((CochainScalarConstruction.underlying R).obj M0) ≫
          prod.map eR.inv (eI.inv.app M0) ≫
            msmul RI (I.modules.obj M0) ≫ eI.hom.app M0 := by
      apply (cancel_mono (eI.inv.app M0)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph F eR.inv (eI.inv.app M0) (eI.inv.app M0)
        (msmul R M0) (msmul RI (I.modules.obj M0))
        (fun U x y ↦ @SMul.smul (R.obj.obj U) (M0.val.obj U) inferInstance x y)
        (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.modules.obj M0).val.obj U)
          inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T a x z hz U t ↦ I.moduleSMul M0 T a x z hz U t)
    set_option backward.isDefEq.respectTransparency false in
    have hm : adj.homEquiv _ _ (eI.inv.app M0 ≫ α) = E M0 H0 α ≫ eP.hom.app H0 :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app M0) (eP.app H0) α
    have hAdd := binary_mate_iso_iff adj (eI.app M0) (eI.app M0) (eI.app M0)
      (eP.hom.app H0) (eP.hom.app H0) (eP.app H0) (madd R M0)
      (madd RI (I.modules.obj M0)) (madd RI H0) (madd R (P.obj H0))
      hLA (hOps H0).1 α α α (E M0 H0 α) (E M0 H0 α) (E M0 H0 α) hm hm hm
    have hSmul := binary_mate_iso_iff adj eR (eI.app M0) (eI.app M0)
      (adj.homEquiv _ _ eR.inv) (eP.hom.app H0) (eP.app H0)
      (msmul R M0) (msmul RI (I.modules.obj M0)) (msmul RI H0) (msmul R (P.obj H0))
      hLS (hOps H0).2 (𝟙 (rset RI)) α α (𝟙 (rset R))
      (E M0 H0 α) (E M0 H0 α) (by simp) hm hm
    have hSame := linear_iff (𝟙 R) M0 (P.obj H0)
      (madd R M0) (madd R (P.obj H0)) (msmul R M0) (msmul R (P.obj H0))
      (madd_spec R M0) (madd_spec R (P.obj H0))
      (msmul_spec R M0) (msmul_spec R (P.obj H0)) (E M0 H0 α)
    exact (linear_iff (𝟙 RI) (I.modules.obj M0) H0 (madd RI (I.modules.obj M0))
      (madd RI H0) (msmul RI (I.modules.obj M0)) (msmul RI H0)
      (madd_spec RI (I.modules.obj M0)) (madd_spec RI H0)
      (msmul_spec RI (I.modules.obj M0)) (msmul_spec RI H0) α).trans
        ((and_congr hAdd hSmul).trans hSame.symm)
  let B := fun M H ↦ restrictHomEquiv (underlying RI) (underlying R) (E M H)
    (hImage M H)
  have hB M H (f : I.modules.obj M ⟶ H) :
      (underlying R).map (B M H f) = E M H ((underlying RI).map f) :=
    restrictHomEquiv_map (underlying RI) (underlying R) (E M H) (hImage M H) f
  have hBL {M N : SheafOfModules.{u} (ringSheaf R)} (a : M ⟶ N)
      (H : SheafOfModules.{u} (ringSheaf RI)) (f : I.modules.obj N ⟶ H) :
      B M H (I.modules.map a ≫ f) = a ≫ B N H f := by
    apply (underlying R).map_injective
    simp only [hB, Functor.map_comp]
    dsimp only [E, mateIsoEquiv, Equiv.trans_apply]
    simp only [Equiv.coe_fn_mk]
    change adj.homEquiv _ _ ((eI.inv.app M ≫
      (underlying RI).map (I.modules.map a)) ≫ (underlying RI).map f) ≫ eP.inv.app H =
        (underlying R).map a ≫
          (adj.homEquiv _ _ (eI.inv.app N ≫ (underlying RI).map f) ≫ eP.inv.app H)
    have hn : eI.inv.app M ≫ (underlying RI).map (I.modules.map a) =
        F.map ((underlying R).map a) ≫ eI.inv.app N :=
      (eI.inv.naturality a).symm
    rw [hn, Category.assoc, adj.homEquiv_naturality_left, Category.assoc]
  have hBR (M : SheafOfModules.{u} (ringSheaf R))
      {H H' : SheafOfModules.{u} (ringSheaf RI)} (f : I.modules.obj M ⟶ H)
      (b : H ⟶ H') : B M H' (f ≫ b) = B M H f ≫ P.map b := by
    apply (underlying R).map_injective
    simp only [hB, Functor.map_comp]
    dsimp only [E, mateIsoEquiv, Equiv.trans_apply]
    simp only [Equiv.coe_fn_mk]
    change adj.homEquiv _ _ (eI.inv.app M ≫
      ((underlying RI).map f ≫ (underlying RI).map b)) ≫ eP.inv.app H' =
        (adj.homEquiv _ _ (eI.inv.app M ≫ (underlying RI).map f) ≫ eP.inv.app H) ≫
          (underlying R).map (P.map b)
    rw [← Category.assoc, adj.homEquiv_naturality_right, Category.assoc,
      Category.assoc]
    exact congrArg (fun k ↦ adj.homEquiv _ _
      (eI.inv.app M ≫ (underlying RI).map f) ≫ k) (eP.inv.naturality b)
  refine ⟨P, ⟨Adjunction.mkOfHomEquiv ?_⟩⟩
  exact
    { homEquiv := B
      homEquiv_naturality_left_symm := by
        intro M N H a f
        apply (B M H).injective
        rw [Equiv.apply_symm_apply, hBL, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ hBR _ f b }

end SheafOfModules.CochainInversePairing
