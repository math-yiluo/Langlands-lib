/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat

/-! # Tensor compatibility of the normalized scalar/pullback comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Binary scalar/pullback tensor coherence with categorical parameters shared.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-pullback-tensor-coherence). -/
def ScalarPullbackTensorLaw
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    (Q : C ⥤ D) (Q' : E ⥤ F) (L : C ⥤ E) (L' : D ⥤ F)
    (a : Q ⋙ L' ≅ L ⋙ Q')
    (dQ : Functor.uncurry.obj (curriedTensor C) ⋙ Q ≅
      Q.prod Q ⋙ Functor.uncurry.obj (curriedTensor D))
    (dQ' : Functor.uncurry.obj (curriedTensor E) ⋙ Q' ≅
      Q'.prod Q' ⋙ Functor.uncurry.obj (curriedTensor F))
    (dL : ∀ P R : C, L.obj (P ⊗ R) ≅ L.obj P ⊗ L.obj R)
    (dL' : ∀ P R : D, L'.obj (P ⊗ R) ≅ L'.obj P ⊗ L'.obj R) : Prop :=
  ∀ P R, a.hom.app (P ⊗ R) ≫ Q'.map (dL P R).hom ≫
      dQ'.hom.app (L.obj P, L.obj R) =
    L'.map (dQ.hom.app (P, R)) ≫ (dL' (Q.obj P) (Q.obj R)).hom ≫
      (a.hom.app P ⊗ₘ a.hom.app R)

/-- The normalized scalar/pullback isomorphism respects the binary tensor comparison.
Source: Stacks 07A4, 0G7E and 0GL6
(blueprint: lem-pur-etale-scalar-pullback-tensor-coherence).
Proof: choose flat K-flat representatives P and Q. Pullback preserves flat K-flat
complexes, and scalar extension on these models is ordinary extension of scalars.
Use the defining scalar/pullback representative square and the defining tensor
representative squares for scalar extension and geometric pullback. On a pair
of homogeneous local pure tensors, both composites send
((p tensor q) tensor b) to (f*p tensor b) tensor (f*q tensor 1).
The ordinary balancing relations identify any alternative distribution of b.
The total-complex maps use the same pair of degrees and the same Koszul sign,
so these equalities commute with both differentials. Sheafification preserves
this equality of the balanced morphisms. The representative maps for the chosen
models are invertible, so cancellation gives the displayed equality on the
localized models. Naturality and flat K-flat resolutions in both variables
extend it to arbitrary derived P and Q. This uses no flatness of the coefficient
map, no boundedness, and no properness of f. -/
private def uncurryTensorComparison
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) :
    Functor.uncurry.obj T ⋙ F ⟶ (F.prod F) ⋙ Functor.uncurry.obj S where
  app Z := (t.app Z.1).app Z.2
  naturality X Y f := by
    have h := (Functor.uncurry.map t).naturality f
    change (F.map ((T.map f.1).app X.2) ≫
      F.map ((T.obj Y.1).map f.2)) ≫ (t.app Y.1).app Y.2 = _ at h
    change F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2) ≫ _ = _
    rw [F.map_comp]
    exact h

private lemma uncurryCurriedTensor_map
    {C : Type*} [Category C] [MonoidalCategory C]
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (Functor.uncurry.obj (curriedTensor C)).map (Prod.mkHom f g) = f ⊗ₘ g := by
  simp only [Functor.uncurry_obj_map, MonoidalCategory.tensorHom_def]
  rw [curriedTensor_obj_map, curriedTensor_map_app]

private theorem natTrans_ext_flat
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{u + 1} C] {D : Type*} [Category D]
    {F G : DerivedCategory C × DerivedCategory C ⥤ D} (α β : F ⟶ G)
    (h : ∀ P Q : CochainComplex C ℤ,
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      α.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        β.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : α = β := by
  ext ⟨U, V⟩
  obtain ⟨P, p, hp, hPflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage U)
  obtain ⟨Q, q, hq, hQflat, hQ⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage V)
  have := hp
  have := hq
  let eP := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso U
  let eQ := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso V
  apply (cancel_epi (F.mapIso (eP.prod eQ)).hom).1
  change F.map (Prod.mkHom eP.hom eQ.hom) ≫ α.app (U, V) =
    F.map (Prod.mkHom eP.hom eQ.hom) ≫ β.app (U, V)
  rw [α.naturality, β.naturality, h P Q hP hQ hPflat hQflat]

theorem etaleScalarPullback_tensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ScalarPullbackTensorLaw (scalarExtension φ Y) (scalarExtension φ X)
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
      (scalarPullbackIso φ f) (ExceptionalCoefficients.tensorIso φ Y)
      (ExceptionalCoefficients.tensorIso φ X)
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) f) := by
  let QY := scalarExtension φ Y
  let QX := scalarExtension φ X
  let LA := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let LB := (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
  let TY := Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) Y)
  let TX := Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) X)
  let dQY := ExceptionalCoefficients.tensorIso φ Y
  let dQX := ExceptionalCoefficients.tensorIso φ X
  let dLA := uncurryTensorComparison LA
    (derivedTensor (ModuleCat.{u + 1} A) Y)
    (derivedTensor (ModuleCat.{u + 1} A) X)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
  let dLB := uncurryTensorComparison LB
    (derivedTensor (ModuleCat.{u + 1} B) Y)
    (derivedTensor (ModuleCat.{u + 1} B) X)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) f)
  let a := scalarPullbackIso φ f
  let α : TY ⋙ QY ⋙ LB ⟶
      (LA.prod LA) ⋙ (QX.prod QX) ⋙ TX :=
    Functor.whiskerLeft TY a.hom ≫
      Functor.whiskerRight dLA QX ≫
      Functor.whiskerLeft (LA.prod LA) dQX.hom
  let β : TY ⋙ QY ⋙ LB ⟶
      (LA.prod LA) ⋙ (QX.prod QX) ⋙ TX :=
    Functor.whiskerRight dQY.hom LB ≫
      Functor.whiskerLeft (QY.prod QY) dLB ≫
      Functor.whiskerRight (NatTrans.prod a.hom a.hom) TX
  have hab : α = β := by
    apply natTrans_ext_flat α β
    intro P R hP hR hPflat hRflat
    have h := etaleScalarPullback_tensor_kFlat φ f P R hP hR hPflat hRflat
    simpa only [α, β, QY, QX, LA, LB, TY, TX, dQY, dQX, dLA, dLB, a,
      uncurryTensorComparison,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.comp_obj, Functor.prod_obj, derivedTensor,
      curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
      Functor.uncurry_obj_obj,
      Functor.uncurry_obj_map, NatTrans.prod, uncurryCurriedTensor_map,
      MonoidalCategory.tensorHom_def, Category.assoc] using h
  intro P R
  have hcomp := congrArg (fun t ↦ t.app (P, R)) hab
  simpa only [α, β, QY, QX, LA, LB, TY, TX, dQY, dQX, dLA, dLB, a,
    uncurryTensorComparison,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_obj, Functor.prod_obj, derivedTensor,
    curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    Functor.uncurry_obj_obj,
    Functor.uncurry_obj_map, Functor.uncurry_map_app,
    NatTrans.prod, uncurryCurriedTensor_map, leftDerivedUpperStarTensorIso_hom,
    MonoidalCategory.tensorHom_def,
    Category.assoc] using hcomp

end AlgebraicGeometry.Etale
