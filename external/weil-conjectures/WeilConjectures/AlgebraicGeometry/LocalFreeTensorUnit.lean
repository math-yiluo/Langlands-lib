/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The tensor sheafification unit on a finite free neighborhood
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

private theorem isIso_toSheafify_app_of_over_isSheaf
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (Y : C)
    (hP : Presheaf.IsSheaf (J.over Y) ((Over.forget Y).op ⋙ P))
    (T : C) (f : T ⟶ Y) : IsIso ((CategoryTheory.toSheafify J P).app (op T)) := by
  let F : Sheaf (J.over Y) AddCommGrpCat.{u + 1} := ⟨_, hP⟩
  let G := ((Over.forget Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (J.over Y) J).obj ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj P)
  let β : F ⟶ G := ⟨Functor.whiskerLeft (Over.forget Y).op
    (CategoryTheory.toSheafify J P)⟩
  have hi := Presheaf.isLocallyInjective_whisker (J.over Y) J
    (Over.forget Y) (CategoryTheory.toSheafify J P)
  have hs := Presheaf.isLocallySurjective_whisker (J.over Y) J
    (Over.forget Y) (CategoryTheory.toSheafify J P)
  have hβ : IsIso β := (Sheaf.isLocallyBijective_iff_isIso β).mp ⟨hi, hs⟩
  have : IsIso β.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map β))
  exact inferInstanceAs (IsIso (β.hom.app (op (Over.mk f))))

section LocalTensor

open scoped ChangeOfRings

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (α : R ⟶ S)
  (V : X.ProEt)
  (M : SheafOfModules.{u + 1} ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over V)))
  [∀ Y : Over V, HasSheafify (((Scheme.ProEt.topology X).over V).over Y)
    AddCommGrpCat.{u + 1}]
  [∀ Y : Over V, (((Scheme.ProEt.topology X).over V).over Y).WEqualsLocallyBijective
    AddCommGrpCat.{u + 1}]
  (q : M.LocalGeneratorsData.{v}) [q.IsLocallyFreeData] (i : q.I)
  [Fintype (q.generators i).I] [DecidableEq (q.generators i).I]

private noncomputable def localIntegralCoordinates (T : (Over (q.X i))ᵒᵖ) :
    M.val.obj (op T.unop.left) ≃ₗ[R.obj.obj (op T.unop.left.left)]
      ((q.generators i).I → R.obj.obj (op T.unop.left.left)) :=
  SheafOfModules.sectionsLinearEquivOfIsoFree (asIso (q.generators i).π).symm T

private noncomputable def localTensorSectionIso (T : (Over (q.X i))ᵒᵖ) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap α V) M).obj (op T.unop.left) ≅
    (SheafOfModules.free (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i)))
        (q.generators i).I).val.obj T := by
  let φ : R.obj.obj (op T.unop.left.left) →+* S.obj.obj (op T.unop.left.left) :=
    ((latticeScalarMap α V).hom.app (op T.unop.left)).hom
  letI := φ.toAlgebra
  let eR : M.val.obj (op T.unop.left) ≃ₗ[R.obj.obj (op T.unop.left.left)]
      ((q.generators i).I → R.obj.obj (op T.unop.left.left)) :=
    localIntegralCoordinates V M q i T
  let eS : (SheafOfModules.free (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i)))
        (q.generators i).I).val.obj T ≃ₗ[S.obj.obj (op T.unop.left.left)]
      ((q.generators i).I → S.obj.obj (op T.unop.left.left)) :=
    SheafOfModules.freeSectionsLinearEquiv (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i)))
      (q.generators i).I T
  let e1 := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (S.obj.obj (op T.unop.left.left)) (S.obj.obj (op T.unop.left.left))) eR
  let e2 := TensorProduct.piRight (R.obj.obj (op T.unop.left.left))
    (S.obj.obj (op T.unop.left.left)) (S.obj.obj (op T.unop.left.left))
    (fun _ : (q.generators i).I ↦ R.obj.obj (op T.unop.left.left))
  let e3 := LinearEquiv.piCongrRight (fun _ : (q.generators i).I ↦
    TensorProduct.AlgebraTensorModule.rid (R.obj.obj (op T.unop.left.left))
      (S.obj.obj (op T.unop.left.left)) (S.obj.obj (op T.unop.left.left)))
  exact (e1.trans (e2.trans (e3.trans eS.symm))).toModuleIso

private theorem localIntegralCoordinates_naturality {T T' : (Over (q.X i))ᵒᵖ}
    (g : T ⟶ T') (m : M.val.obj (op T.unop.left)) (j : (q.generators i).I) :
    localIntegralCoordinates V M q i T'
      (M.val.map ((Over.forget (q.X i)).op.map g) m) j =
      R.obj.map ((Over.forget V).op.map ((Over.forget (q.X i)).op.map g))
        (localIntegralCoordinates V M q i T m j) := by
  have hp := PresheafOfModules.naturality_apply (asIso (q.generators i).π).inv.val g m
  have hf := PresheafOfModules.naturality_apply
    (SheafOfModules.freeπ (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over V)).over (q.X i))) j).val
    g ((asIso (q.generators i).π).inv.val.app T m)
  exact (congrArg (fun z ↦
    (SheafOfModules.freeπ (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over V)).over (q.X i))) j).val.app
        T' z) hp).trans hf

private theorem localTensorSectionIso_coordinate (T : (Over (q.X i))ᵒᵖ)
    (j : (q.generators i).I) (s : S.obj.obj (op T.unop.left.left))
    (m : M.val.obj (op T.unop.left)) :
    (SheafOfModules.freeπ (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i))) j).val.app T
        ((localTensorSectionIso α V M q i T).hom
          (s ⊗ₜ[R.obj.obj (op T.unop.left.left),
            ((latticeScalarMap α V).hom.app (op T.unop.left)).hom] m)) =
      s * (α.hom.app (op T.unop.left.left)) (localIntegralCoordinates V M q i T m j) := by
  let φ : R.obj.obj (op T.unop.left.left) →+* S.obj.obj (op T.unop.left.left) :=
    ((latticeScalarMap α V).hom.app (op T.unop.left)).hom
  let := φ.toAlgebra
  let eS := SheafOfModules.freeSectionsLinearEquiv (R := (((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i)))
    (q.generators i).I T
  change eS (eS.symm (fun k ↦ φ (localIntegralCoordinates V M q i T m k) * s)) j = _
  exact (congrFun (eS.apply_symm_apply
    (fun k ↦ φ (localIntegralCoordinates V M q i T m k) * s)) j).trans
      (mul_comm (φ (localIntegralCoordinates V M q i T m j)) s)

private noncomputable def localTensorPresheafIso :
    (Over.forget (q.X i)).op ⋙
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (latticeScalarMap α V) M).presheaf ≅
    (SheafOfModules.free (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i)))
        (q.generators i).I).val.presheaf := by
  refine NatIso.ofComponents (fun T ↦
    (forget₂ (ModuleCat (S.obj.obj (op T.unop.left.left))) AddCommGrpCat).mapIso
      (localTensorSectionIso α V M q i T)) ?_
  intro T T' g
  ext z
  let g₀ := (Over.forget (q.X i)).op.map g
  let g₁ := (Over.forget V).op.map g₀
  change (localTensorSectionIso α V M q i T').hom
    (SheafOfModules.changeOfRingsMap (latticeScalarMap α V) M g₀ z) =
    (SheafOfModules.free (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i)))
        (q.generators i).I).val.map g ((localTensorSectionIso α V M q i T).hom z)
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s m =>
    have ht := Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap (latticeScalarMap α V) M g₀) s m
    change SheafOfModules.changeOfRingsMap (latticeScalarMap α V) M g₀
      (s ⊗ₜ[R.obj.obj (op T.unop.left.left),
        ((latticeScalarMap α V).hom.app (op T.unop.left)).hom] m) = _ at ht
    refine (congrArg (localTensorSectionIso α V M q i T').hom ht).trans ?_
    apply (SheafOfModules.freeSectionsLinearEquiv (R := (((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i)))
      (q.generators i).I T').injective
    funext j
    have hl := localTensorSectionIso_coordinate α V M q i T' j
      (S.obj.map g₁ s) (M.val.map g₀ m)
    have hr := localTensorSectionIso_coordinate α V M q i T j s m
    have hc := localIntegralCoordinates_naturality V M q i g m j
    have ha : α.hom.app (op T'.unop.left.left)
        (R.obj.map g₁ (localIntegralCoordinates V M q i T m j)) =
        S.obj.map g₁ (α.hom.app (op T.unop.left.left)
          (localIntegralCoordinates V M q i T m j)) :=
      ConcreteCategory.congr_hom (α.hom.naturality g₁)
        (localIntegralCoordinates V M q i T m j)
    have hn := PresheafOfModules.naturality_apply
      (SheafOfModules.freeπ (R := (((sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over V)).over (q.X i))) j).val g
      ((localTensorSectionIso α V M q i T).hom
        (s ⊗ₜ[R.obj.obj (op T.unop.left.left),
          ((latticeScalarMap α V).hom.app (op T.unop.left)).hom] m))
    let s' : S.obj.obj (op T'.unop.left.left) := S.obj.map g₁ s
    exact hl.trans ((congrArg (fun z : R.obj.obj (op T'.unop.left.left) ↦ s' *
      α.hom.app (op T'.unop.left.left) z) hc).trans
      ((congrArg (fun z : S.obj.obj (op T'.unop.left.left) ↦ s' * z) ha).trans
        (((S.obj.map g₁).hom.map_mul s _).symm.trans
          ((congrArg (S.obj.map g₁) hr.symm).trans hn.symm))))

end LocalTensor

/-- On an object factoring through a finite free neighborhood, the sectionwise tensor
product already computes sheafified scalar extension.
Source: Bhatt--Scholze, Proposition 6.8.4(6), finite free local bases, and Stacks, Tag 03EK.
(auxiliary; not a blueprint node).
Proof: restrict the tensor presheaf to the given free neighborhood. The finite free
coordinate isomorphism identifies it with a finite product of the target ring sheaf,
so it is a sheaf there. The sheafification unit is locally bijective, also after
restriction to this slice. A locally bijective map between sheaves is an isomorphism.
Evaluate this isomorphism at the given factoring object. Empty objects and empty bases
are included in the finite product argument. -/
theorem localFreeTensorUnit_isIso {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (α : R ⟶ S)
    (V : X.ProEt)
    (M : SheafOfModules.{u + 1} ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over V)))
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (W : X.ProEt) (a : W ⟶ V) (t : Over.mk a ⟶ q.X i) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (S.over V)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (latticeScalarMap α V) M)).app (op (Over.mk a))) := by
  classical
  have hs₀ : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  have hs₁ : ∀ Y : X.ProEt, HasSheafify ((Scheme.ProEt.topology X).over Y)
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have hs₂ : ∀ Y : Over V, HasSheafify (((Scheme.ProEt.topology X).over V).over Y)
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have hw₁ : ∀ Y : X.ProEt, ((Scheme.ProEt.topology X).over Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have hw₂ : ∀ Y : Over V, (((Scheme.ProEt.topology X).over V).over Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType i
  let : Fintype (q.generators i).I := Fintype.ofFinite (q.generators i).I
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    (latticeScalarMap α V) M
  let E := localTensorPresheafIso α V M q i
  have hP : Presheaf.IsSheaf (((Scheme.ProEt.topology X).over V).over (q.X i))
      ((Over.forget (q.X i)).op ⋙ P.presheaf) :=
    (Presheaf.isSheaf_of_iso_iff E).mpr (SheafOfModules.free
      (R := (((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (S.over V)).over (q.X i))) (q.generators i).I).isSheaf
  have hunit := isIso_toSheafify_app_of_over_isSheaf
    ((Scheme.ProEt.topology X).over V) P.presheaf (q.X i) hP (Over.mk a) t
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over V)).obj)).unit.app P).app (op (Over.mk a))
  have : IsIso ((forget₂ (ModuleCat (S.obj.obj (op W))) AddCommGrpCat).map η) := hunit
  exact isIso_of_reflects_iso η
    (forget₂ (ModuleCat (S.obj.obj (op W))) AddCommGrpCat)

end AlgebraicGeometry.ProEtale
