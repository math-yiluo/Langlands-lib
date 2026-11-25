/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # Tensor product of scalar section morphisms

Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV.
(blueprint: lem-sc-scalar-tensor-global-sections-morphism).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory


private local instance (X : Scheme.{w}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

private theorem scalarUnit_ε
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    Functor.LaxMonoidal.ε
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)) ≫
      (scalarUnitMorphism f).hom =
      ((CategoryTheory.sheafificationAdjunction
        (Opens.grothendieckTopology X) (ModuleCat.{w} k)).homEquiv _ _)
        (((constantSheafAdj (Opens.grothendieckTopology X)
          (ModuleCat.{w} k) isTerminalTop).homEquiv (ModuleCat.of k k)
            (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf))).symm (scalarUnitLinear f)) := by
  let J := Opens.grothendieckTopology X
  let L := presheafToSheaf J (ModuleCat.{w} k)
  let R := sheafToPresheaf J (ModuleCat.{w} k)
  let adj := CategoryTheory.sheafificationAdjunction J (ModuleCat.{w} k)
  unfold scalarUnitMorphism constantScalarUnitIso
  change Functor.LaxMonoidal.ε R ≫ R.map (Functor.LaxMonoidal.ε L ≫ _) = _
  rw [Functor.map_comp, ← Category.assoc]
  have he : Functor.LaxMonoidal.ε R ≫ R.map (Functor.LaxMonoidal.ε L) =
      adj.unit.app (𝟙_ ((TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{w} k)) := by
    change adj.homEquiv _ _ (Functor.OplaxMonoidal.η L) ≫ R.map _ = _
    rw [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.Monoidal.η_ε,
      ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom]
    exact Category.comp_id _
  rw [he]
  rfl

private theorem scalarUnit_ε_app
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (r : k) :
    ((Functor.LaxMonoidal.ε
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)) ≫
      (scalarUnitMorphism f).hom).app (op U)) r = scalarMap f U r := by
  rw [scalarUnit_ε]
  simp only [constantSheafAdj, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  erw [Equiv.apply_symm_apply]
  erw [Adjunction.homEquiv_counit]
  change scalarRestriction f (SheafOfModules.unit X.ringCatSheaf)
    (isTerminalTop.from U).op (scalarUnitLinear f r) = scalarMap f U r
  change (X.presheaf.map (isTerminalTop.from U).op).hom (scalarMap f ⊤ r) = _
  simp only [scalarMap, RingHom.comp_apply]
  change (X.presheaf.map (homOfLE (le_top : ⊤ ≤ ⊤)).op ≫
    X.presheaf.map (isTerminalTop.from U).op).hom
      ((f.appTop).hom ((ΓSpecIso (CommRingCat.of k)).inv.hom r)) = _
  rw [← X.presheaf.map_comp]
  rfl

private theorem scalarSection_ε_app
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules)
    (s : scalarObj f F (op ⊤)) (U : X.Opens) (r : k) :
    ((Functor.LaxMonoidal.ε
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)) ≫
      (scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection F s)).hom).app (op U)) r =
      (scalarMap f U r) • F.presheaf.map (homOfLE le_top).op s := by
  change (Functor.LaxMonoidal.ε
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)) ≫
    (scalarUnitMorphism f).hom ≫ (scalarHom f (homOfGlobalSection F s)).hom).app (op U) r = _
  rw [← Category.assoc]
  change Hom.app (homOfGlobalSection F s) U
    (((Functor.LaxMonoidal.ε
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)) ≫
      (scalarUnitMorphism f).hom).app (op U)) r) = _
  rw [scalarUnit_ε_app, homOfGlobalSection_app]

private theorem inclusion_unit_inv
    {k : Type w} [Field k] {X : Scheme.{w}} :
    let R := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)
    Functor.LaxMonoidal.ε R ≫ R.map (λ_ (𝟙_ (KSheaf X k))).inv =
      (λ_ (𝟙_ ((TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{w} k))).inv ≫
        (Functor.LaxMonoidal.ε R ⊗ₘ Functor.LaxMonoidal.ε R) ≫
        Functor.LaxMonoidal.μ R (𝟙_ (KSheaf X k)) (𝟙_ (KSheaf X k)) := by
  dsimp only
  rw [← Functor.LaxMonoidal.left_unitality_inv]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [tensorHom_def', Category.assoc]

/-- Scalar section morphisms respect the tensor coefficient.
Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV.
(blueprint: lem-sc-scalar-tensor-global-sections-morphism).

Proof: Precompose both morphisms with the constant-scalar-unit isomorphism.
The constant-sheaf/global-sections adjunction reduces equality to the linear maps
out of k determined by the value at one. Each section morphism sends one to its
section: scalarUnitLinear sends one to one, and homOfGlobalSection evaluates to
its section at the top open. The inverse unit constraint sends one to the pure
tensor one tensor one under the inclusion tensorator. Naturality of this
tensorator therefore identifies the tensor of the two section morphisms at one
with the tensorator applied to s tensor t. The already proved
exists_scalarTensorCoefficient sends this to tmulSection s t, the same value as
the section morphism on the right. Linear maps out of k are determined by one,
and the adjunction and unit isomorphism are injective, proving the equality.
The proof remains valid for zero sections and for the empty scheme. -/
theorem scalarTensorCoefficient_globalSections_morphism
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules)
    (s : scalarObj f F (op ⊤)) (t : scalarObj f G (op ⊤)) :
    (λ_ (𝟙_ (KSheaf X k))).inv ≫
        ((scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection F s)) ⊗ₘ
          (scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection G t))) ≫
        scalarTensorCoefficient f F G =
      scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection (F ⊗ G) (tmulSection s t)) := by
  let R := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)
  let α := scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection F s)
  let β := scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection G t)
  apply Sheaf.hom_ext_of_ε_comp
  change Functor.LaxMonoidal.ε R ≫
    R.map ((λ_ (𝟙_ (KSheaf X k))).inv ≫ (α ⊗ₘ β) ≫
      scalarTensorCoefficient f F G) = _
  have h : Functor.LaxMonoidal.ε R ≫
      R.map ((λ_ (𝟙_ (KSheaf X k))).inv ≫ (α ⊗ₘ β) ≫
        scalarTensorCoefficient f F G) =
      (λ_ (𝟙_ ((TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{w} k))).inv ≫
        ((Functor.LaxMonoidal.ε R ≫ R.map α) ⊗ₘ
          (Functor.LaxMonoidal.ε R ≫ R.map β)) ≫
        Functor.LaxMonoidal.μ R (scalarSheaf f F) (scalarSheaf f G) ≫
        R.map (scalarTensorCoefficient f F G) := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, inclusion_unit_inv]
    simp only [Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_assoc]
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rfl
  rw [h]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (scalarTensorCoefficient f F G).hom.app U
    ((Functor.LaxMonoidal.μ R (scalarSheaf f F) (scalarSheaf f G)).app U
      (((Functor.LaxMonoidal.ε R ≫ R.map α).app U ⊗ₘ
        (Functor.LaxMonoidal.ε R ≫ R.map β).app U)
          ((λ_ (ModuleCat.of k k)).inv r))) = _
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  have hF : (Functor.LaxMonoidal.ε R ≫ R.map α).app U (1 : k) =
      (scalarMap f U.unop 1) • F.presheaf.map (homOfLE le_top).op s :=
    scalarSection_ε_app f F s U.unop 1
  have hG : (Functor.LaxMonoidal.ε R ≫ R.map β).app U r =
      (scalarMap f U.unop r) • G.presheaf.map (homOfLE le_top).op t :=
    scalarSection_ε_app f G t U.unop r
  have hFG : (Functor.LaxMonoidal.ε R ≫
      R.map (scalarUnitMorphism f ≫
        scalarHom f (homOfGlobalSection (F ⊗ G) (tmulSection s t)))).app U r =
      (scalarMap f U.unop r) • (F ⊗ G).presheaf.map (homOfLE le_top).op
        (tmulSection s t) :=
    scalarSection_ε_app f (F ⊗ G) (tmulSection s t) U.unop r
  rw [hF, hG, hFG]
  simp only [map_one, one_smul]
  exact (exists_scalarTensorCoefficient f F G U.unop
    (F.presheaf.map (homOfLE le_top).op s)
    ((scalarMap f U.unop r) • G.presheaf.map (homOfLE le_top).op t)).trans
      (by rw [tmulSection_smul, tmulSection_map])

end
end AlgebraicGeometry.Scheme.Modules
