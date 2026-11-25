/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorNormalization
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.QuotientPullbackTensorFlatModel

/-! # Tensor coherence of the normalized quotient pullback comparison

The positive exponent is n + 1, including the residue-field quotient at n = 0.
The section comparison is specified by its ordinary ringed-square balancing map
and localization counits, rather than by an arbitrary isomorphism of functors.

## References

* Tags 0D6D and 07A4

## Implementation details

In `quotient_pullback_tensor_coherence` the section composition comparison is characterized by
`SectionPullNormalized`: its ordinary map is the conjugate of `pullIso`, and its derived map is
fixed by the two composite localization counits on every flat-term K-flat model. This is the
normalization used in `integral_quotient_direct_image_comparison`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

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

private theorem natTrans_ext_flat
    {C D : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v} C] [Category.{w} D]
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

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

open QuotientChange QuotientSectionTensor

/-- The derived tensor comparison `leftDerivedUpperStarTensor` for the pullback functor
`L B f`. -/
@[irreducible] def quotientTensorPull
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (L B f)).obj (CondensedRing.derivedTensor B Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (L B f)).obj (L B f)).obj
        (CondensedRing.derivedTensor B X) := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarTensor B f

/-- The actual quotient coefficient square commutes, its normalized pullback
comparison realizes the ringed-square composition comparison, and that same
comparison intertwines the two composite tensorators on all unbounded inputs. -/
theorem quotient_pullback_tensor_coherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (integral l E) T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (finite l E n) T)]
    (b : ∀ T : Scheme.{u}, TensorIso (reduction l E n) T)
    (_hb : ∀ T : Scheme.{u}, QuotientSectionTensor.TensorNormalized
      (reduction l E n) T (b T))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D (reduction l E n) Y ⋙ L (finite l E n) f ≅
      L (integral l E) f ⋙ D (reduction l E n) X)
    (_hlam : PullNormalized (reduction l E n) f lam) :
    (ProEtale.upperStar Ab.{u + 1} f).map (coefficientMap (reduction l E n) Y) ≫
        condensedPullbackHom (finite l E n) f =
      condensedPullbackHom (integral l E) f ≫ coefficientMap (reduction l E n) X ∧
    (∃ (cX : ScalarSectionData (reduction l E n) X)
        (cY : ScalarSectionData (reduction l E n) Y),
      ScalarSectionNormalized (reduction l E n) X cX ∧
      ScalarSectionNormalized (reduction l E n) Y cY ∧
      ∃ barLam : cY.model.T ⋙ ModuleRingedComparison.derivedPullback (finite l E n) f ≅
          ModuleRingedComparison.derivedPullback (integral l E) f ⋙ cX.model.T,
        PullSectionCondition (reduction l E n) f cX cY lam barLam ∧
        SectionPullNormalized (reduction l E n) f cX cY barLam) ∧
    ∀ U V : DerivedCategory (Modules (integral l E) Y),
      lam.hom.app (U ⊗ V) ≫
          (D (reduction l E n) X).map
            (((quotientTensorPull (integral l E) f).app U).app V) ≫
          (b X).hom.app ((L (integral l E) f).obj U, (L (integral l E) f).obj V) =
        (L (finite l E n) f).map ((b Y).hom.app (U, V)) ≫
          ((quotientTensorPull (finite l E n) f).app
            ((D (reduction l E n) Y).obj U)).app ((D (reduction l E n) Y).obj V) ≫
          (lam.hom.app U ⊗ₘ lam.hom.app V) := by
  refine ⟨map_coefficientMap_comp_condensedPullbackHom (reduction l E n) f, ?_, ?_⟩
  · obtain ⟨c, hc, _, _, _, hpull⟩ :=
      (quotient_section_tensor_normalization l E n).2 b _hb
    obtain ⟨barLam, hbarLam, hbarNormalized⟩ := hpull f lam _hlam
    exact ⟨c X, c Y, hc X, hc Y, barLam, hbarLam, hbarNormalized⟩
  · let TY := Functor.uncurry.obj (CondensedRing.derivedTensor (integral l E) Y)
    let TX := Functor.uncurry.obj (CondensedRing.derivedTensor (finite l E n) X)
    let DY := D (reduction l E n) Y
    let DX := D (reduction l E n) X
    let LR := L (integral l E) f
    let LS := L (finite l E n) f
    let tR := uncurryTensorComparison LR
      (CondensedRing.derivedTensor (integral l E) Y)
      (CondensedRing.derivedTensor (integral l E) X) (quotientTensorPull (integral l E) f)
    let tS := uncurryTensorComparison LS
      (CondensedRing.derivedTensor (finite l E n) Y)
      (CondensedRing.derivedTensor (finite l E n) X) (quotientTensorPull (finite l E n) f)
    let lhs : TY ⋙ (DY ⋙ LS) ⟶ ((LR ⋙ DX).prod (LR ⋙ DX)) ⋙ TX :=
      Functor.whiskerLeft TY lam.hom ≫
        Functor.whiskerRight tR DX ≫ Functor.whiskerLeft (LR.prod LR) (b X).hom
    let rhs : TY ⋙ (DY ⋙ LS) ⟶ ((LR ⋙ DX).prod (LR ⋙ DX)) ⋙ TX :=
      Functor.whiskerRight (b Y).hom LS ≫
        Functor.whiskerLeft (DY.prod DY) tS ≫
        Functor.whiskerRight (NatTrans.prod lam.hom lam.hom) TX
    have h : lhs = rhs := by
      apply natTrans_ext_flat (C := Modules (integral l E) Y) lhs rhs
      intro P Q hP hQ hPflat hQflat
      dsimp only [lhs, rhs, TY, TX, DY, DX, LR, LS, tR, tS,
        uncurryTensorComparison, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
      unfold quotientTensorPull
      convert quotient_pullback_tensor_flat_model l E n b _hb f lam _hlam
        P Q hP hQ hPflat hQflat using 1 <;>
        simp only [id_eq, Functor.prod_obj, NatTrans.prod] <;>
        unfold L CondensedRing.moduleObjectDerivedPullback <;> rfl
    intro U V
    simpa only [lhs, rhs, TY, TX, DY, DX, LR, LS, tR, tS, uncurryTensorComparison,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.uncurry_obj_obj, Functor.uncurry_obj_map, Functor.prod_obj,
      Functor.comp_obj, NatTrans.prod, CondensedRing.derivedTensor,
      curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
      ← MonoidalCategory.tensorHom_def] using NatTrans.congr_app h (U, V)

end AlgebraicGeometry.ProEtale.IntegralQuotient
