/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.CategoryTheory.RingedScalarTensorComparison
import all WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.CategoryTheory.RingedScalarTensorSections

/-! # The ordinary scalar tensor comparison preserves insertion of one

Source: Stacks Project, Tags 03EK and 03CZ.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
open AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.CochainPullback

namespace CategoryTheory.ConstantCompletion

variable {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
  {R S : Sheaf T CommRingCat.{w}}

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
attribute [local implicit_reducible] SheafOfModules.unit SheafOfModules.restrictScalars
  CategoryTheory.sheafCompose change PresheafOfModules.restrictScalars
  PresheafOfModules.toPresheaf

/-- The section one defines the ordinary coefficient insertion. -/
def scalarTensorCoefficientUnit (f : R ⟶ S) :
    ringedSiteRingComplex R ⟶
      (HomologicalComplex.single _ (.up ℤ) 0).obj (scalarTensorModule f) :=
  (HomologicalComplex.single _ (.up ℤ) 0).map
    ((scalarTensorModule f).unitHomEquiv.symm
      ⟨fun V ↦ (1 : S.obj.obj V), fun {V W} a ↦ by
        change S.obj.map a 1 = 1
        exact map_one _⟩)

/-- Tensor insertion of one, before localization. -/
def scalarTensorUnit (f : R ⟶ S) (P : Cx R) :
    P ⟶ ((ringedKoszulTensor R).obj P).obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (scalarTensorModule f)) :=
  (ringedKoszulRightUnitIso R P).inv ≫
    ((ringedKoszulTensor R).obj P).map (scalarTensorCoefficientUnit f)

private theorem single_inv (N : Mod R) (P : Cx R) (q : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso
      (letI := SheafOfModules.monoidalCategory R; curriedTensor (Mod R)) N P).inv.f q =
    (letI := SheafOfModules.monoidalCategory R
     (P.X q ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv) ≫
       HomologicalComplex.ιMapBifunctor P
         ((HomologicalComplex.single _ (.up ℤ) 0).obj N)
         (curriedTensor (Mod R)) (.up ℤ) q 0 q (by simp)) := by
  let := SheafOfModules.monoidalCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  dsimp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_inv,
    HomologicalComplex.comp_f, Iso.symm_inv]
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  simp

private theorem single_second {N N' : Mod R} (g : N ⟶ N') (P : Cx R) (q : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod R)) N P).inv.f q ≫
        (((ringedKoszulTensor R).obj P).map
          ((HomologicalComplex.single _ (.up ℤ) 0).map g)).f q =
      (P.X q ◁ g) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod R)) N' P).inv.f q := by
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  rw [single_inv N P q, single_inv N' P q]
  change (_ ≫ _) ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P)
    ((HomologicalComplex.single _ (.up ℤ) 0).map g)
    (curriedTensor (Mod R)) (.up ℤ)).f q = _
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  rw [HomologicalComplex.id_f, Functor.map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  rw [HomologicalComplex.single_map_f_self]
  change (P.X q ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv) ≫
      (P.X q ◁ ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom ≫ g ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N').inv)) ≫ _ = _
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_inv_hom_assoc]

/-- The explicit ordinary comparison identifies the two insertion-of-one maps.
There is no derived functor, K-flatness hypothesis, inverse limit or tower here.

Source: Stacks Project, Modules on Sites, Tag 03EK, tensor cancellation identity;
Modules on Sites, Tag 03CZ, lemma-adjointness-tensor-restrict.
(auxiliary; not a blueprint node).

Proof: evaluate the maps of complexes in degree q. The right unitor includes the
(q,0) summand, and the single-complex contraction in scalarTensorComplexIso
projects back to that summand; all other summands are zero. On that summand the
coefficient unit takes x to x tensor 1. Symmetry takes it to 1 tensor x. The inverse
of the normalized cancellation isomorphism takes this to 1 tensor (1 tensor x),
and the left unitor takes it to 1 tensor x in scalar extension. This is precisely
adicFiniteOrdinaryUnit, by its insertion normalization. The section formula of
exists_changeOfRings_tensorCancellation_sections proves the cancellation equation.
Equality after the presheaf tensor sheafification unit suffices by the sheafification
adjunction; pure tensors suffice there by tensor induction. Thus equality holds
in each degree and hence for the chain maps. The proof also covers zero modules,
zero rings, and unbounded complexes, since each degree uses only the (q,0) summand. -/
theorem scalarTensorComplexIso_unit (f : R ⟶ S) (P : Cx R) :
    scalarTensorUnit f P ≫ (scalarTensorComplexIso f P).hom =
      adicFiniteOrdinaryUnitComplex f P := by
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  let sectionOne : (scalarTensorModule f).sections :=
    ⟨fun V ↦ (1 : S.obj.obj V), fun {V W} a ↦ by
      change S.obj.map a 1 = 1
      exact map_one _⟩
  let g : SheafOfModules.unit (siteModuleRings R) ⟶ scalarTensorModule f :=
    (scalarTensorModule f).unitHomEquiv.symm sectionOne
  have hg (V : Cᵒᵖ) : g.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V) :=
    congrArg (fun s ↦ s.val V)
      ((scalarTensorModule f).unitHomEquiv.apply_symm_apply sectionOne)
  apply (cancel_mono (scalarTensorComplexIso f P).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro q
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have ho : ((adicFiniteOrdinaryUnit f).app (P.X q)).val.app V x =
      tensorSection f (P.X q) V 1 x := by
    have h := congrArg (fun k ↦ k.hom.app V x)
      ((adicFiniteOrdinaryUnit_existsUnique f).exists.choose_spec (P.X q))
    exact h.trans (adicFiniteInsertion_apply f (P.X q) V x)
  have hi : (scalarTensorModuleIso f (P.X q)).inv.val.app V
      (tensorSection f (P.X q) V 1 x) =
      moduleTmul (R := R) (P.X q) (scalarTensorModule f) V x (1 : S.obj.obj V) := by
    rw [← scalarTensorModuleIso_pure f (P.X q) V x (1 : S.obj.obj V)]
    exact congrArg (fun k ↦ k.val.app V
      (moduleTmul (R := R) (P.X q) (scalarTensorModule f) V x (1 : S.obj.obj V)))
      (scalarTensorModuleIso f (P.X q)).hom_inv_id
  change (((ringedKoszulRightUnitIso R P).inv.f q) ≫
      (((ringedKoszulTensor R).obj P).map (scalarTensorCoefficientUnit f)).f q).val.app V x =
    ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod R))
      (scalarTensorModule f) P).inv.f q).val.app V
        ((scalarTensorModuleIso f (P.X q)).inv.val.app V
          (((adicFiniteOrdinaryUnit f).app (P.X q)).val.app V x))
  rw [ho, hi]
  have hu : (ringedKoszulRightUnitIso R P).inv.f q =
      (ρ_ (P.X q)).inv ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod R))
          (SheafOfModules.unit (siteModuleRings R)) P).inv.f q := by
    rw [single_inv]
    exact HomologicalComplex.rightUnitor'_inv P q
  rw [hu, Category.assoc]
  unfold scalarTensorCoefficientUnit
  rw [single_second]
  change ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod R))
    (scalarTensorModule f) P).inv.f q).val.app V
      ((P.X q ◁ g).val.app V ((ρ_ (P.X q)).inv.val.app V x)) = _
  apply congrArg (((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod R))
    (scalarTensorModule f) P).inv.f q).val.app V)
  rw [scalarTensorRightUnit_pure (P.X q) V x]
  rw [← id_tensorHom]
  have hm := moduleTmul_map (R := R) (𝟙 (P.X q)) g V x (1 : R.obj.obj V)
  simpa only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply, hg]
    using hm

end CategoryTheory.ConstantCompletion
