/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.SecSmoothPurity.CochainInverseComparison
import all WeilConjectures.SecSmoothPurity.CochainModuleAdjunction
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence

/-! # Module adjunction with its underlying topos transpose
Source: Stacks Project, Modules on Sites, Tags 03D3 and 03D7.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace WeilConjectures.SemilinearSections
open SheafOfModules SheafOfModules.CochainInversePairing
open CochainGeometricConstruction GeometricConstruction CochainScalarConstruction
attribute [local irreducible] monoidalCategory
set_option autoImplicit false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The module adjunction for a specified algebraic inverse image, with the
underlying transpose retained. Source: Stacks 03D3 and 03D7.
(auxiliary; not a blueprint node).

Proof: use the existing product-preserving right-module construction. Its addition
and scalar diagrams identify linear maps among the set-sheaf adjuncts. Restrict the
set adjunction to those maps. Faithfulness proves the two inverse laws and naturality;
the resulting Hom equivalence defines the adjunction. Its map formula is exactly the
underlying set adjunction, followed by the inverse underlying-sheaf identification. -/
theorem normalizedModuleAdjunction_exists
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : F ⊣ V) [PreservesFiniteLimits F]
    (I : AlgebraicInverseImage F R RI) :
    ∃ P : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RI) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      ∃ (eP : P ⋙ toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u}) ≅
          (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ V)
        (a : I.modules ⊣ P),
        ∀ M H (f : I.modules.obj M ⟶ H),
          (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map
              (a.homEquiv M H f) ≫ eP.hom.app H =
            adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫
              (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map f) := by
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
  let B := fun M H ↦ CochainInversePairing.restrictHomEquiv (underlying RI) (underlying R) (E M H)
    (hImage M H)
  have hB M H (f : I.modules.obj M ⟶ H) :
      (underlying R).map (B M H f) = E M H ((underlying RI).map f) :=
    CochainInversePairing.restrictHomEquiv_map (underlying RI) (underlying R) (E M H) (hImage M H) f
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
  let core : Adjunction.CoreHomEquiv I.modules P :=
    { homEquiv := B
      homEquiv_naturality_left_symm := by
        intro M N H a f
        apply (B M H).injective
        rw [Equiv.apply_symm_apply, hBL, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ hBR _ f b }
  refine ⟨P, eP, Adjunction.mkOfHomEquiv core, ?_⟩
  intro M H f
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change (underlying R).map (B M H f) ≫ eP.hom.app H = _
  rw [hB]
  exact (mateIsoEquiv_equation adj (eI.app M) (eP.app H)
    ((underlying RI).map f)).symm

end WeilConjectures.SemilinearSections
