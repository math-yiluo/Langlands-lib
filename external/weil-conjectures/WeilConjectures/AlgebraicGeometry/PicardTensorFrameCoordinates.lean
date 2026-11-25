/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Explicit coordinates on tensor pullbacks of framed sheaves

Source: Stacks Project, Tags 0096 and 01CA.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The canonical tensor-unit isomorphism, with the pinned adjoint structure map. -/
def picardTensorFrameUnitIso {X Y : Scheme.{v}} (g : X ⟶ Y) :
    (tensorPullback g).obj (Modules.unit Y) ≅ Modules.unit X := by
  haveI := (tensorPullbackObjUnitToUnit_isIso g).1
  exact asIso (tensorPullbackObjUnitToUnit g)

/-- The tensor pullback of a free sheaf, normalized on each summand by the unit map. -/
def picardTensorFreeIso {X Y : Scheme.{v}} (g : X ⟶ Y) (I : Type v) :
    (tensorPullback g).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I := by
  letI := (Classical.choose (exists_tensorPullbackAdjunction g)).isLeftAdjoint
  exact (SheafOfModules.mapFreeIso (tensorPullback g) I (picardTensorFrameUnitIso g).symm).symm

/-- Morphisms from the structure sheaf are additive global-section coordinates. -/
def picardUnitHomTopEquiv {X : Scheme.{v}} (M : X.Modules) :
    (Modules.unit X ⟶ M) ≃+ Γ(M, ⊤) where
  toFun f := (SheafOfModules.unitHomEquiv M f).val (.op ⊤)
  invFun x := (SheafOfModules.unitHomEquiv M).symm
    (M.val.sectionsMk
      (fun V ↦ M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op x)
      (fun V W k ↦ by rw [← M.val.map_comp_apply]; congr 1))
  left_inv f := by
    apply (SheafOfModules.unitHomEquiv M).injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    exact PresheafOfModules.sections_property _ _
  right_inv x := by
    dsimp only
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 _) x = x
    simp
  map_add' f g := rfl

/-- Conjugation by two isomorphisms is an additive equivalence of morphism groups. -/
def picardHomCongr {X : Scheme.{v}} {M M' N N' : X.Modules}
    (a : M ≅ M') (b : N ≅ N') : (M ⟶ N) ≃+ (M' ⟶ N') where
  toFun f := a.inv ≫ f ≫ b.hom
  invFun f := a.hom ≫ f ≫ b.inv
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp [Preadditive.comp_add, Preadditive.add_comp]

/-- Coordinates of a raw morphism into the tensor pullback of a rank-one frame. -/
def picardTensorScalarCoordinate {W Y T : Scheme.{v}}
    (t : T ⟶ W) (s : T ⟶ Y) {M : Y.Modules} (q : M ≅ Modules.unit Y) :
    ((tensorPullback t).obj (Modules.unit W) ⟶ (tensorPullback s).obj M) ≃+
      Γ(T, ⊤) :=
  (picardHomCongr (picardTensorFrameUnitIso t)
    ((tensorPullback s).mapIso q ≪≫ picardTensorFrameUnitIso s)).trans
      (picardUnitHomTopEquiv (Modules.unit T))

/-- Coordinates of a raw morphism into the tensor pullback of a finite-rank frame. -/
def picardTensorVectorCoordinate {W Y T : Scheme.{v}}
    (t : T ⟶ W) (s : T ⟶ Y) {M : Y.Modules} (m : ℕ)
    (q : M ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{v} (Fin m))) :
    ((tensorPullback t).obj (Modules.unit W) ⟶ (tensorPullback s).obj M) ≃+
      (Fin m → Γ(T, ⊤)) :=
  ((picardHomCongr (picardTensorFrameUnitIso t)
    ((tensorPullback s).mapIso q ≪≫ picardTensorFreeIso s (ULift.{v} (Fin m)))).trans
      ((picardUnitHomTopEquiv _).trans (freeSectionsEquiv _).toAddEquiv)).trans
        { toFun := fun a i ↦ a ⟨i⟩
          invFun := fun a i ↦ a i.down
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl }

private lemma tensorUnit_conj_app_top {X Y : Scheme.{v}} (g : X ⟶ Y)
    (f : Modules.unit Y ⟶ Modules.unit Y) :
    Hom.app ((picardTensorFrameUnitIso g).inv ≫ (tensorPullback g).map f ≫
        (picardTensorFrameUnitIso g).hom) ⊤ (1 : Γ(X, ⊤)) =
      g.appTop (Hom.app f ⊤ (1 : Γ(Y, ⊤))) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  set F := (picardTensorFrameUnitIso g).inv ≫ (tensorPullback g).map f ≫
    (picardTensorFrameUnitIso g).hom
  have hF : (tensorPullback g).map f ≫ (picardTensorFrameUnitIso g).hom =
      (picardTensorFrameUnitIso g).hom ≫ F := by simp [F]
  have key := congrArg (adj.homEquiv _ _) hF
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at key
  have h2 : adj.homEquiv _ _ (picardTensorFrameUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    (adj.homEquiv _ _).apply_symm_apply _
  rw [h2] at key
  have he := congrArg (fun (φ : Modules.unit Y ⟶ (pushforward g).obj (Modules.unit X)) ↦
    Hom.app φ ⊤ (1 : Γ(Y, ⊤))) key
  dsimp only at he
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at he
  have e1 : Hom.app (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ⊤
      (1 : Γ(Y, ⊤)) = (1 : Γ(X, ⊤)) := map_one g.appTop.hom
  exact (he.trans (congrArg (Hom.app F (g ⁻¹ᵁ ⊤)) e1)).symm

private lemma tensorFree_hom_projection {X Y : Scheme.{v}} (g : X ⟶ Y)
    (I : Type v) [DecidableEq I] (i : I) :
    (picardTensorFreeIso g I).hom ≫ freeπ i =
      (tensorPullback g).map (freeπ i) ≫ (picardTensorFrameUnitIso g).hom := by
  let := (Classical.choose (exists_tensorPullbackAdjunction g)).isLeftAdjoint
  apply (cancel_epi (picardTensorFreeIso g I).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply free_hom_ext
  intro j
  have hι : SheafOfModules.ιFree j ≫ (picardTensorFreeIso g I).inv =
      (picardTensorFrameUnitIso g).inv ≫ (tensorPullback g).map (SheafOfModules.ιFree j) := by
    exact SheafOfModules.ιFree_mapFreeIso_hom _ _ _ _
  rw [reassoc_of% hι, ← Functor.map_comp_assoc, ιFree_freeπ,
    ιFree_freeπ]
  split_ifs <;> simp

private lemma tensorColumn_app_top {X Y : Scheme.{v}} (g : X ⟶ Y)
    (I : Type v) [Fintype I] [DecidableEq I]
    (φ : Modules.unit Y ⟶ SheafOfModules.free (R := Y.ringCatSheaf) I) (i : I) :
    freeSectionsEquiv I
      (Hom.app ((picardTensorFrameUnitIso g).inv ≫ (tensorPullback g).map φ ≫
        (picardTensorFreeIso g I).hom) ⊤ (1 : Γ(X, ⊤))) i =
      g.appTop (freeSectionsEquiv I (Hom.app φ ⊤ (1 : Γ(Y, ⊤))) i) := by
  change Hom.app (freeπ i) ⊤ (Hom.app _ ⊤ _) =
    g.appTop (Hom.app (freeπ i) ⊤ (Hom.app φ ⊤ _))
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Category.assoc,
    Category.assoc, tensorFree_hom_projection, ← Functor.map_comp_assoc]
  exact tensorUnit_conj_app_top g (φ ≫ freeπ i)

/-- Tensor pullback applies the structure-ring map to a framed column morphism.
Source: Stacks Project, Tags 0096 and 01CA.
(blueprint: lem-sc-picard-tensor-frame-map)

Proof: The chosen tensor adjunction makes tensor pullback preserve coproducts.
The free comparison is characterized on the inclusions by the pinned tensor-unit
map. Conjugating a pulled-back endomorphism of the unit by that unit comparison
applies s.appTop to its value at one: apply the adjunction to the conjugation
square and evaluate its unit on one. Compose with each coordinate projection of
the target free sheaf. Linearity says that postcomposition on a section multiplies
its scalar by the pulled-back column entry. These equalities in all coordinates
prove the displayed formula. No affineness or perfectness is used. When m=0,
both sides are the unique empty vector. -/
theorem picardTensorFrame_map {W Y T : Scheme.{v}}
    (t : T ⟶ W) (s : T ⟶ Y) {M N : Y.Modules}
    (q0 : M ≅ Modules.unit Y) (m : ℕ)
    (q1 : N ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{v} (Fin m)))
    (δ : M ⟶ N)
    (f : (tensorPullback t).obj (Modules.unit W) ⟶ (tensorPullback s).obj M) :
    picardTensorVectorCoordinate t s m q1 (f ≫ (tensorPullback s).map δ) =
      picardTensorScalarCoordinate t s q0 f •
        (fun i ↦ s.appTop
          (freeSectionsEquiv (ULift.{v} (Fin m))
            (Hom.app (q0.inv ≫ δ ≫ q1.hom) ⊤ (1 : Γ(Y, ⊤))) ⟨i⟩)) := by
  classical
  let φ := q0.inv ≫ δ ≫ q1.hom
  let u := (picardTensorFrameUnitIso t).inv ≫ f ≫
    (tensorPullback s).map q0.hom ≫ (picardTensorFrameUnitIso s).hom
  let a : Γ(T, ⊤) := Hom.app u ⊤ (1 : Γ(T, ⊤))
  let v := (picardTensorFrameUnitIso s).inv ≫ (tensorPullback s).map φ ≫
    (picardTensorFreeIso s (ULift.{v} (Fin m))).hom
  have hc : (picardTensorFrameUnitIso t).inv ≫ (f ≫ (tensorPullback s).map δ) ≫
      ((tensorPullback s).mapIso q1 ≪≫ picardTensorFreeIso s (ULift.{v} (Fin m))).hom =
        u ≫ v := by
    simp only [u, v, φ, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_assoc]
    have hcancel := ((tensorPullback s).mapIso q0).hom_inv_id
    dsimp only [Functor.mapIso_hom, Functor.mapIso_inv] at hcancel
    rw [reassoc_of% hcancel]
  change (fun i ↦ freeSectionsEquiv (ULift.{v} (Fin m))
    (Hom.app ((picardTensorFrameUnitIso t).inv ≫
      (f ≫ (tensorPullback s).map δ) ≫
      ((tensorPullback s).mapIso q1 ≪≫
        picardTensorFreeIso s (ULift.{v} (Fin m))).hom) ⊤ (1 : Γ(T, ⊤))) ⟨i⟩) = _
  rw [hc]
  have hv : Hom.app (u ≫ v) ⊤ (1 : Γ(T, ⊤)) = a • Hom.app v ⊤ (1 : Γ(T, ⊤)) := by
    change Hom.app v ⊤ a = _
    simpa only [smul_eq_mul, mul_one] using
      Hom.app_smul v (U := ⊤) a (1 : Γ(T, ⊤))
  rw [hv, (freeSectionsEquiv (ULift.{v} (Fin m))).map_smul a _]
  ext i
  change a * _ = _
  rw [tensorColumn_app_top]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
