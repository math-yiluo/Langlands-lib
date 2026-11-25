/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionInterchangeCore
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.NormalizedProjectionAdjunctionTranspose
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TensorShiftNaturality
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ProjectionNaturality
import all WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveNormalizedUnitCounitRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided

/-! Tensor-strength compatibility of the canonical projection mates. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

private theorem projection_transpose
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) (adj : F ⊣ R)
    (δ : ∀ U V : C, F.obj (U ⊗ V) ⟶ F.obj U ⊗ F.obj V) (U : C) (V : D) :
    F.map (AlgebraicGeometry.ProEtale.CondensedRing.traceProjectionFromComparison
        adj δ U V) ≫ adj.counit.app _ =
      δ U (R.obj V) ≫ (F.obj U ◁ adj.counit.app V) := by
  simpa only [AlgebraicGeometry.ProEtale.CondensedRing.traceProjectionFromComparison,
    Adjunction.homEquiv_counit, id_tensorHom, Functor.id_obj] using
    (adj.homEquiv _ _).symm_apply_apply
      (δ U (R.obj V) ≫ (F.obj U ◁ adj.counit.app V))

private theorem tensorator_swap
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal]
    (hb : ∀ U V : C, F.map (β_ U V).hom ≫ Functor.OplaxMonoidal.δ F V U =
      Functor.OplaxMonoidal.δ F U V ≫ (β_ (F.obj U) (F.obj V)).hom)
    (A B Q : C) :
    F.map ((α_ A B Q).hom ≫ (A ◁ (β_ B Q).hom) ≫ (α_ A Q B).inv) ≫
        Functor.OplaxMonoidal.δ F (A ⊗ Q) B ≫
        (Functor.OplaxMonoidal.δ F A Q ▷ F.obj B) =
      Functor.OplaxMonoidal.δ F (A ⊗ B) Q ≫
        (Functor.OplaxMonoidal.δ F A B ▷ F.obj Q) ≫
        (α_ (F.obj A) (F.obj B) (F.obj Q)).hom ≫
        (F.obj A ◁ (β_ (F.obj B) (F.obj Q)).hom) ≫
        (α_ (F.obj A) (F.obj Q) (F.obj B)).inv := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.associativity_inv]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [← whiskerLeft_comp_assoc, hb, whiskerLeft_comp_assoc]
  rw [← Functor.OplaxMonoidal.associativity_assoc]

private theorem projection_swap
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [F.OplaxMonoidal] (adj : F ⊣ R)
    (hb : ∀ U V : C, F.map (β_ U V).hom ≫ Functor.OplaxMonoidal.δ F V U =
      Functor.OplaxMonoidal.δ F U V ≫ (β_ (F.obj U) (F.obj V)).hom)
    (π : ∀ (U : C) (V : D), U ⊗ R.obj V ⟶ R.obj (F.obj U ⊗ V))
    (hπ : ∀ U V, F.map (π U V) ≫ adj.counit.app _ =
      Functor.OplaxMonoidal.δ F U (R.obj V) ≫ (F.obj U ◁ adj.counit.app V))
    (A B : C) (N : D) :
    (α_ A B (R.obj N)).hom ≫ (A ◁ (β_ B (R.obj N)).hom) ≫
        (α_ A (R.obj N) B).inv ≫ (π A N ▷ B) ≫
        ((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app
          (F.obj A ⊗ N)).app B =
      π (A ⊗ B) N ≫ R.map
        ((Functor.OplaxMonoidal.δ F A B ▷ N) ≫
          (α_ (F.obj A) (F.obj B) N).hom ≫
          (F.obj A ◁ (β_ (F.obj B) N).hom) ≫
          (α_ (F.obj A) N (F.obj B)).inv) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj.map_rightAdjointProjectionMap_app_app_comp_counit]
  simp only [Functor.OplaxMonoidal.δNatTrans_app_app, curriedTensor_map_app]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [← comp_whiskerRight, hπ, comp_whiskerRight]
  rw [reassoc_of% (hπ (A ⊗ B) N)]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (tensorator_swap F hb A B (R.obj N))]
  rw [← associator_inv_naturality_middle]
  rw [← whiskerLeft_comp_assoc, ← BraidedCategory.braiding_naturality_right,
    whiskerLeft_comp_assoc]
  rw [← associator_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rfl

private theorem swap_middle
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (A B B' N : C) (e : B ⟶ B') :
    ((A ◁ e) ▷ N) ≫ (α_ A B' N).hom ≫
        (A ◁ (β_ B' N).hom) ≫ (α_ A N B').inv =
      (α_ A B N).hom ≫ (A ◁ (β_ B N).hom) ≫
        (α_ A N B).inv ≫ ((A ⊗ N) ◁ e) := by
  rw [associator_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_left,
    whiskerLeft_comp_assoc]
  rw [associator_inv_naturality_right]

private theorem strength_transport
    {C D : Type*} [Category C] [Category D]
    [mC : MonoidalCategory C] [bC : BraidedCategory C]
    [mD : MonoidalCategory D] [bD : BraidedCategory D]
    (F : C ⥤ D) (R : D ⥤ C) (H : C ⥤ C) (J : D ⥤ D)
    (A B : C) (T N V : D) (x : F.obj A ⊗ N ⟶ V)
    (e : F.obj B ≅ T)
    (a : ∀ U : C, U ⊗ B ≅ H.obj U) (b : ∀ W : D, W ⊗ T ≅ J.obj W)
    (d : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (π : ∀ U : C, U ⊗ R.obj N ⟶ R.obj (F.obj U ⊗ N))
    (ρ : ∀ W : D, R.obj W ⊗ B ⟶ R.obj (W ⊗ F.obj B))
    (ha : (π A ≫ R.map x) ▷ B ≫ (a (R.obj V)).hom =
      (a (A ⊗ R.obj N)).hom ≫ H.map (π A ≫ R.map x))
    (hb : x ▷ T ≫ (b V).hom = (b (F.obj A ⊗ N)).hom ≫ J.map x)
    (hρ : (R.map x ▷ B) ≫ ρ V = ρ (F.obj A ⊗ N) ≫ R.map (x ▷ F.obj B))
    (hπ : ((a A).inv ▷ R.obj N) ≫ π (A ⊗ B) =
      π (H.obj A) ≫ R.map (F.map (a A).inv ▷ N))
    (hs : (α_ A B (R.obj N)).hom ≫ (A ◁ (β_ B (R.obj N)).hom) ≫
        (α_ A (R.obj N) B).inv ≫ (π A ▷ B) ≫ ρ (F.obj A ⊗ N) =
      π (A ⊗ B) ≫ R.map
        ((d.hom ▷ N) ≫ (α_ (F.obj A) (F.obj B) N).hom ≫
          (F.obj A ◁ (β_ (F.obj B) N).hom) ≫ (α_ (F.obj A) N (F.obj B)).inv)) :
    ((a A).inv ▷ R.obj N) ≫ (α_ A B (R.obj N)).hom ≫
        (A ◁ (β_ B (R.obj N)).hom) ≫ (α_ A (R.obj N) B).inv ≫
        (a (A ⊗ R.obj N)).hom ≫ H.map (π A ≫ R.map x) ≫
        (a (R.obj V)).inv ≫ ρ V ≫ R.map ((V ◁ e.hom) ≫ (b V).hom) =
      π (H.obj A) ≫ R.map
        (((F.mapIso (a A).symm ≪≫ d ≪≫ tensorIso (Iso.refl _) e ≪≫ b (F.obj A)).hom ▷
            N) ≫ ((b (F.obj A)).inv ▷ N) ≫
          (α_ (F.obj A) T N).hom ≫ (F.obj A ◁ (β_ T N).hom) ≫
          (α_ (F.obj A) N T).inv ≫ (b (F.obj A ⊗ N)).hom ≫ J.map x) := by
  rw [← reassoc_of% ha]
  simp only [comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hρ, reassoc_of% hs, reassoc_of% hπ]
  simp only [← R.map_comp, Category.assoc]
  congr 1
  apply congrArg R.map
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, id_tensorHom, comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc (b (F.obj A)).hom,
    Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  rw [← whisker_exchange_assoc]
  rw [← reassoc_of% (swap_middle (F.obj A) (F.obj B) T N e.hom)]
  rw [hb]

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local implicit_reducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The native braiding through the fixed tensor bundle. -/
@[irreducible]
def tensorBraiding
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B : DerivedCategory (Modules Λ X)) : A ⊗ B ≅ B ⊗ A := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  exact traceBraiding Λ X A B

@[instance_reducible]
private def tensorBraided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    BraidedCategory (DerivedCategory (Modules Λ Z)) := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  letI : SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab.{u + 1} Z }
  exact DerivedCategory.braidedCategory' (Modules Λ Z)

private theorem tensorBraided_braiding
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u})
    (A B : DerivedCategory (Modules Λ Z)) :
    @BraidedCategory.braiding _ _ (internalMonoidal Λ Z) (tensorBraided Λ Z) A B =
      tensorBraiding Λ Z A B := by
  unfold tensorBraided tensorBraiding
  rfl

private theorem secondTraceBraided_braiding
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (A B : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    @BraidedCategory.braiding _ _ (internalMonoidal Λ (ProjectiveLine Y))
        (secondTraceBraided Λ Y) A B = tensorBraiding Λ (ProjectiveLine Y) A B := by
  unfold secondTraceBraided
  simpa only [tensorBraiding] using (tensorBraided_braiding Λ (ProjectiveLine Y) A B)

section NativeComparison

-- Comparing the native and bundled tensor structures needs more elaboration fuel.
private theorem normalized_projection_swap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (π : ProjectionFamily Λ) (hπ : ProjectionNormalized Λ π)
    (ρ : ProjectionMateFamily Λ) (hρ : ProjectionMateNormalized Λ ρ) :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (A B : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X)),
    (α_ A B ((moduleObjectDerivedPushforward Λ f).obj N)).hom ≫
        (A ◁ (tensorBraiding Λ S B ((moduleObjectDerivedPushforward Λ f).obj N)).hom) ≫
        (α_ A ((moduleObjectDerivedPushforward Λ f).obj N) B).inv ≫
        (π f A N ▷ B) ≫
        ρ f ((moduleObjectDerivedPullback Λ f).obj A ⊗ N) B =
      π f (A ⊗ B) N ≫ (moduleObjectDerivedPushforward Λ f).map
        (((nativeProjectionTensorIso Λ f A B).hom ▷ N) ≫
          (α_ ((moduleObjectDerivedPullback Λ f).obj A)
            ((moduleObjectDerivedPullback Λ f).obj B) N).hom ≫
          ((moduleObjectDerivedPullback Λ f).obj A ◁
            (tensorBraiding Λ X ((moduleObjectDerivedPullback Λ f).obj B) N).hom) ≫
          (α_ ((moduleObjectDerivedPullback Λ f).obj A) N
            ((moduleObjectDerivedPullback Λ f).obj B)).inv) := by
  intro X S f A B N
  have hpA := normalized_projection_transpose Λ π hπ f A N
  have hpAB := normalized_projection_transpose Λ π hπ f (A ⊗ B) N
  have hρ0 := hρ f ((moduleObjectDerivedPullback Λ f).obj A ⊗ N) B
  dsimp only [ProjectionNormalized, ProjectionFamily, ProjectionMateNormalized,
    ProjectionMateFamily, tensorBraiding, nativeProjectionTensorIso, traceTensorComparison,
    traceBraiding, traceDerivedBraiding, internalMonoidal, internalTensorBundle,
    nativeTensorBundle, moduleObjectDerivedPullback, moduleObjectDerivedPushforward,
    projectionDerivedMonoidal] at *
  have hpA' := eq_of_heq hpA
  have hpAB' := eq_of_heq hpAB
  with_unfolding_all have hρ' := eq_of_heq hρ0
  erw [hpA', hpAB', hρ']
  dsimp only [Iso.app, asIso, id]
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) :=
    { sheafSymmetricCategory S with toBraidedCategory := sheafBraidedCategory Ab.{u + 1} S }
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    { sheafSymmetricCategory X with toBraidedCategory := sheafBraidedCategory Ab.{u + 1} X }
  let : MonoidalCategory (DerivedCategory (Modules Λ S)) := projectionDerivedMonoidal Λ S
  let : MonoidalCategory (DerivedCategory (Modules Λ X)) := projectionDerivedMonoidal Λ X
  let : BraidedCategory (DerivedCategory (Modules Λ S)) :=
    DerivedCategory.braidedCategory' (Modules Λ S)
  let : BraidedCategory (DerivedCategory (Modules Λ X)) :=
    DerivedCategory.braidedCategory' (Modules Λ X)
  let := leftDerivedUpperStarOplaxMonoidal Λ f
  let F := (CondensedRing.upperStar Λ f).leftDerivedFunctor
  let R := (CondensedRing.lowerStar Λ f).rightDerivedFunctor
  with_unfolding_all
    let adj : F ⊣ R := CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
  let π₀ := traceProjectionFromComparison (F := F) (P := R) adj
    (Functor.OplaxMonoidal.δ F)
  have hπ₀ (U : DerivedCategory (Modules Λ S)) (V : DerivedCategory (Modules Λ X)) :
      F.map (π₀ U V) ≫ adj.counit.app _ =
        Functor.OplaxMonoidal.δ F U (R.obj V) ≫ (F.obj U ◁ adj.counit.app V) := by
    exact projection_transpose F R adj (Functor.OplaxMonoidal.δ F) U V
  unfold traceAdjunction tracePull tracePush moduleObjectProjectionMate
    moduleObjectDerivedTensorComparison
  with_unfolding_all
    exact projection_swap F R adj (leftDerivedUpperStarTensor_braiding Λ f) π₀ hπ₀ A B N

end NativeComparison

section FinalTransport

-- Compare the fixed tensor and shift structures once when specializing abstract coherence.
/-- Tensor strength can be moved through a projection and an arbitrary inside arrow. -/
theorem second_trace_strength_projection_action
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y X : Scheme.{u})
    (f : X ⟶ ProjectiveLine Y)
    (LS : Modules Λ (ProjectiveLine Y)) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS)
        ⟦(2 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧))
    (K : DerivedCategory (Modules Λ Y))
    (N D : DerivedCategory (Modules Λ X))
    (x : (moduleObjectDerivedPullback Λ f).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗ N ⟶ D) :
    let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
    let P := moduleObjectDerivedPullback Λ f
    let R := moduleObjectDerivedPushforward Λ f
    let H := twist Λ (ProjectiveLine Y) LS
    let J := twist Λ X LX
    let T := (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    secondTraceStrengthTail Λ Y LS K (R.obj N) ≫
        H.map (projectionMap Λ f A N ≫ R.map x) ≫
        twistProjectionMap Λ f LS LX e D =
      projectionMap Λ f (H.obj A) N ≫ R.map
        (((pullTwistIso Λ f LS LX e A).hom ▷ N) ≫
          ((tensorShiftIso Λ X LX (P.obj A)).inv ▷ N) ≫
          (α_ (P.obj A) T N).hom ≫
          (P.obj A ◁ (tensorBraiding Λ X T N).hom) ≫
          (α_ (P.obj A) N T).inv ≫
          (tensorShiftIso Λ X LX (P.obj A ⊗ N)).hom ≫ J.map x) := by
  let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  let B := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS)
    ⟦(2 : ℤ)⟧
  let T := ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧
  let F := moduleObjectDerivedPullback Λ f
  let R := moduleObjectDerivedPushforward Λ f
  let H := twist Λ (ProjectiveLine Y) LS
  let J := twist Λ X LX
  let a := tensorShiftIso Λ (ProjectiveLine Y) LS
  let b := tensorShiftIso Λ X LX
  have ha := tensorShiftIso_naturality Λ (ProjectiveLine Y) LS
    (projectionMap Λ f A N ≫ R.map x)
  have hb := tensorShiftIso_naturality Λ X LX x
  have hn := projectionMateMap_naturality Λ f x B
  have hp := projectionMap_naturality Λ f (a A).inv N
  have hs := normalized_projection_swap Λ (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec (projectionMate_existsUnique Λ).exists.choose
    (projectionMate_existsUnique Λ).exists.choose_spec f A B N
  unfold secondTraceStrengthTail twistProjectionMap pullTwistIso
  let := tensorBraided Λ (ProjectiveLine Y)
  let := tensorBraided Λ X
  simpa only [tensorBraided_braiding, secondTraceBraided_braiding, tensorIso_hom,
    Iso.refl_hom, id_tensorHom, tensorHom_id, Category.assoc,
    A, B, T, F, R, H, J, a, b, nativeProjectionTensorIso, id] using
    strength_transport
      (mC := internalMonoidal Λ (ProjectiveLine Y))
      (bC := tensorBraided Λ (ProjectiveLine Y))
      (mD := internalMonoidal Λ X) (bD := tensorBraided Λ X)
      F R H J A B T N D x e a b
      (nativeProjectionTensorIso Λ f A B)
      (fun U ↦ projectionMap Λ f U N) (fun W ↦ projectionMateMap Λ f W B)
      (by simpa only [tensorHom_id] using ha)
      (by simpa only [tensorHom_id] using hb)
      (by simpa only [tensorHom_id] using hn)
      (by simpa only [tensorHom_id] using hp)
      (by simpa only [projectionMap, projectionMateMap, tensorBraided_braiding] using hs)

end FinalTransport

end AlgebraicGeometry.ProEtale.RationalP1
