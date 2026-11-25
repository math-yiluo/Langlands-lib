/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPushSquare
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedSupportedCoefficientTransportNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedAcyclic

/-! # Transporting only the supported coefficient source

Source: diagonal tower coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

section SingleSquares

universe a v w
variable {A B C D : Type a} [Category.{v} A] [Category.{v} B]
  [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
  [F.Additive] [G.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V] in
private theorem cochain_single_square (q : F ⋙ V ≅ U ⋙ G) (M : A) :
    (NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app
        ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (U.obj M) =
    (V.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).hom.app (F.obj M) ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (q.hom.app M) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      CategoryTheory.Functor.map_comp, Category.assoc]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
    simpa only [CategoryTheory.Functor.comp_map, Category.assoc] using!
      congrArg (fun z ↦ z ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((U ⋙ G).obj M)).inv)
        (q.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).symm
  · exact ((F ⋙ V).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)).eq_of_src _ _

private theorem augmentation_eq (R : DiagonalRightDerived F) (M : A) :
    diagonalTraceRightSingle F R M =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        R.η.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) := by
  simp only [diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [R.R.map_id, Category.comp_id]

private theorem single_factors (M : A) :
    (U.mapDerivedCategorySingleFunctor 0).hom.app M =
      U.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) := by
  erw [← U.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M]
  erw [Iso.hom_inv_id_app_assoc]

private theorem restriction_single_square
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (q : F ⋙ V ≅ U ⋙ G)
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG q) (M : A) :
    V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) ≫
        s.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) =
      (V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (q.hom.app M) ≫
        diagonalTraceRightSingle G RG (U.obj M) := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj M
  let cF := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let cG := HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0
  let cU := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
  let cV := HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0
  have hc : (V.mapHomologicalComplex (.up ℤ)).map (cF.inv.app M) ≫
      (NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app K ≫
      (G.mapHomologicalComplex (.up ℤ)).map (cU.hom.app M) =
      cV.hom.app (F.obj M) ≫ (HomologicalComplex.single D (.up ℤ) 0).map
        (q.hom.app M) ≫ cG.inv.app (U.obj M) := by
    apply (cancel_epi ((V.mapHomologicalComplex (.up ℤ)).map (cF.hom.app M))).mp
    apply (cancel_mono (cG.hom.app (U.obj M))).mp
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact cochain_single_square F G U V q M
  rw [augmentation_eq, augmentation_eq, single_factors U, single_factors V]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (s.normalization K)]
  change V.mapDerivedCategory.map (DerivedCategory.Q.map (cF.inv.app M)) ≫
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app K) ≫
      RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
      RG.R.map (DerivedCategory.Q.map (cU.hom.app M)) =
    V.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫
      DerivedCategory.Q.map (cV.hom.app (F.obj M)) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (q.hom.app M)) ≫
      DerivedCategory.Q.map (cG.inv.app (U.obj M)) ≫
      RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M))
  have hn := RG.η.naturality (cU.hom.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [← hn]
  erw [V.mapDerivedCategoryFactors.hom.naturality_assoc (cF.inv.app M)]
  congr 1
  simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp_assoc]
  exact congrArg (fun z ↦ DerivedCategory.Q.map z ≫
    RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M))) hc

private theorem restriction_single_square_inv
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (q : F ⋙ V ≅ U ⋙ G)
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG q) (M : A) :
    diagonalTraceRightSingle G RG (U.obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
        s.iso.inv.app ((DerivedCategory.singleFunctor A 0).obj M) =
      (DerivedCategory.singleFunctor D 0).map (q.inv.app M) ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
        V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) := by
  apply (cancel_mono (s.iso.hom.app _ ≫
    RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [RG.R.map_id, Category.comp_id]
  rw [restriction_single_square F G U V RF RG q s M]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem augmentation_naturality (R : DiagonalRightDerived F)
    {M N : A} (v : M ⟶ N) :
    (DerivedCategory.singleFunctor B 0).map (F.map v) ≫
        diagonalTraceRightSingle F R N =
      diagonalTraceRightSingle F R M ≫ R.R.map
        ((DerivedCategory.singleFunctor A 0).map v) := by
  rw [augmentation_eq, augmentation_eq]
  erw [← DerivedCategory.Q.map_comp_assoc]
  erw [(HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality v]
  erw [DerivedCategory.Q.map_comp, Category.assoc]
  have hn := R.η.naturality
    ((HomologicalComplex.single A (.up ℤ) 0).map v)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [hn]
  rw [Category.assoc]
  rfl

end SingleSquares

universe aa vv ww

private theorem normalized_transport_core
    {A B C D : Type aa} [Category.{vv} A] [Category.{vv} B]
    [Category.{vv} C] [Category.{vv} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{ww} A] [HasDerivedCategory.{ww} B]
    [HasDerivedCategory.{ww} C] [HasDerivedCategory.{ww} D]
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (q : F ⋙ V ≅ U ⋙ G)
    (sq : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG q)
    {M : A} {N : B} {M' : C} {N' : D}
    {P : Prop} {pn : (N ≅ F.obj M) → P → Prop}
    (r : DiagonalTrace.NormalizedSource F RF M N P pn)
    (e : U.obj M ≅ M') (j : V.obj N ≅ N') (t : N' ≅ G.obj M')
    (ht : V.map r.iso.hom ≫ q.hom.app M ≫ G.map e.hom = j.hom ≫ t.hom) :
    IsIso (diagonalTraceRightSingle G RG M') ∧
      V.mapDerivedCategory.map r.hom ≫
          sq.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
          RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
            (DerivedCategory.singleFunctor C 0).map e.hom) =
        (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor D 0).map j.hom ≫
          (DerivedCategory.singleFunctor D 0).map t.hom ≫
          (@AlgebraicGeometry.ProEtale.diagonalTraceRightSingle C _ _ D _ _ _ _ G _ RG M') := by
  have hsq := restriction_single_square F G U V RF RG q sq M
  letI : IsIso (diagonalTraceRightSingle F RF M) := r.acyclic
  have hacyc : IsIso
      (V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M)) := by
    infer_instance
  have hleft : IsIso
      (V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) ≫
        sq.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M)) := by
    infer_instance
  letI : IsIso
      (V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) ≫
        sq.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M)) := hleft
  have hright : IsIso
      ((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (q.hom.app M) ≫
        diagonalTraceRightSingle G RG (U.obj M)) := by
    rw [← hsq]
    infer_instance
  letI : IsIso
      ((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (q.hom.app M) ≫
        diagonalTraceRightSingle G RG (U.obj M)) := hright
  have hUM : IsIso (diagonalTraceRightSingle G RG (U.obj M)) := by
    have hright' : IsIso
        (((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
          (DerivedCategory.singleFunctor D 0).map (q.hom.app M)) ≫
          diagonalTraceRightSingle G RG (U.obj M)) := by
      simpa only [Category.assoc] using hright
    letI := hright'
    exact IsIso.of_isIso_comp_left
      ((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (q.hom.app M))
      (diagonalTraceRightSingle G RG (U.obj M))
  have htrans :
      (DerivedCategory.singleFunctor D 0).map (G.map e.hom) ≫
        diagonalTraceRightSingle G RG M' =
      diagonalTraceRightSingle G RG (U.obj M) ≫
        RG.R.map ((DerivedCategory.singleFunctor C 0).map e.hom) := by
    exact augmentation_naturality G RG e.hom
  have hM' : IsIso (diagonalTraceRightSingle G RG M') := by
    have hc : IsIso
        ((DerivedCategory.singleFunctor D 0).map (G.map e.hom) ≫
          diagonalTraceRightSingle G RG M') := by
      rw [htrans]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.singleFunctor D 0).map (G.map e.hom))
      (diagonalTraceRightSingle G RG M')
  refine ⟨hM', ?_⟩
  dsimp only [DiagonalTrace.NormalizedSource.hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hsq]
  have hn := (V.mapDerivedCategorySingleFunctor 0).hom.naturality r.iso.hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have htrans' := htrans.symm
  rw [htrans']
  have hfinal := congrArg (fun z ↦
      (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor D 0).map z ≫
        diagonalTraceRightSingle G RG M') ht
  simpa only [Functor.map_comp, Category.assoc] using hfinal
/-- The supported coefficient isomorphism is an actual ordinary direct-image
comparison at the diagonal, followed by the regular-unit comparison.
Source: coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport). -/
def completedSupportedCoefficientIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sΔ : CompletedOrdinarySquare l (diagonalImmersion Y) eP eW) :
    eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y :=
  sΔ.ordinary.app (SheafOfModules.unit
    (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≪≫
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (diagonalImmersion Y)).mapIso eP.unitIso

/-- Categorical cancellation for an ordinary square; the heterogeneous form
keeps the source-object equality explicit.
Source: categorical cancellation in the supported-source normalization.
(blueprint: lem-diagonal-completed-supported-transport). -/
private theorem normalized_underlying_square
    {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B T : C} {S : D}
    (u : A ≅ B) (v : S ≅ H.obj B)
    (o : S ⟶ H.obj A) (w : A ⟶ T)
    (h : o ≫ H.map u.hom = v.hom) :
    v.inv ≫ o ≫ H.map w = H.map (u.inv ≫ w) := by
  have ho : v.inv ≫ o = H.map u.inv := by
    apply (cancel_mono (H.map u.hom)).mp
    rw [Category.assoc, h, v.inv_hom_id, ← H.map_comp,
      u.inv_hom_id, H.map_id]
  rw [H.map_comp, ← Category.assoc, ho]

private theorem normalized_underlying_square_heq
    {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B T : C} {S V : D}
    (u : A ≅ B) (v : S ≅ V)
    (o : S ⟶ H.obj A) (w : A ⟶ T)
    (e : V = H.obj B) (h : HEq (o ≫ H.map u.hom) v.hom) :
    HEq (v.inv ≫ o ≫ H.map w) (H.map (u.inv ≫ w)) := by
  subst V
  exact heq_of_eq (normalized_underlying_square H u v o w (eq_of_heq h))

private theorem completed_source_underlying (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (diagonalCompletedRestriction l (diagonalSurface Y) ⋙
        diagonalForget l (diagonalSurface Y)).obj (diagonalCompletedSource l Y) =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj
        ((diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
          diagonalForget l (ProjectiveLine Y)).obj (SheafOfModules.unit
            (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))) := rfl

/-- The explicit supported coefficient isomorphism has the prescribed
underlying-sheaf normalization.

Source: coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport).

Proof: the ordinary diagonal square intertwines the two underlying-sheaf
comparisons. Cancel the image of the regular-module underlying isomorphism,
then compose with the direct image of the regular-unit comparison. -/
theorem completedSupportedCoefficientIso_normalization (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sΔ : CompletedOrdinarySquare l (diagonalImmersion Y) eP eW) :
    HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫
        (completedSupportedCoefficientIso l Y eP eW sΔ).hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom)) := by
  let M := SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
    (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
  let H := lowerStar Ab.{u + 1} (diagonalImmersion Y)
  change HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫
    (sΔ.ordinary.hom.app M).hom ≫ H.map eP.unitIso.hom.hom)
      (H.map (eP.underlying.inv.app M ≫ eP.unitIso.hom.hom))
  exact normalized_underlying_square_heq H (eP.underlying.app M)
    (eW.underlying.app (diagonalCompletedSource l Y))
    (sΔ.ordinary.hom.app M).hom eP.unitIso.hom.hom
    (completed_source_underlying l Y) (sΔ.normalization M)

/-- The constructed supported comparison transports every normalized acyclic
supported source through the universal-unit derived square.
The coefficient realizations and all ordinary squares are inputs, rather than
part of the conclusion. No trace or integration identity occurs.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), supported-source
identification; diagonal trace proof step 9.
(blueprint: lem-diagonal-completed-supported-transport).

Proof: expand the constructed isomorphism. The diagonal ordinary square's
normalization and naturality of the underlying comparison give the displayed
source normalization. For a projection f, transport the ordinary supported
isomorphism using the regular-unit comparison, its ordinary coefficient square,
and the constructed source comparison. On underlying sheaves the composite is
the composition isomorphism for direct images followed by the equality
Delta f = id and the identity direct-image isomorphism. Thus it has the required
support normalization. Apply the full universal-unit equation to the complex
concentrated in degree zero at the supported source. The single-complex and
single-functor comparison isomorphisms identify this equation with the displayed
derived source square. All other arrows in that square are isomorphisms:
exact equivalences preserve the original source's acyclicity, and the endpoint
and derived-square comparisons are isomorphisms. Consequently the condensed
single-object derived unit is an isomorphism. Together with the normalized
ordinary isomorphism this gives the asserted NormalizedSource. -/
theorem completedSupportedCoefficient_transport (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sΔ : CompletedOrdinarySquare l (diagonalImmersion Y) eP eW) :
    let i := completedSupportedCoefficientIso l Y eP eW sΔ
    ∀ (f : diagonalSurface Y ⟶ ProjectiveLine Y)
      (R : DiagonalRightDerived (diagonalTracePush l f))
      (a : DiagonalTrace.SupportedSource l Y f R)
      (s : CompletedOrdinarySquare l f eW eP),
      let R' := canonicalDiagonalRightDerived
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      ∃ b : DiagonalTrace.NormalizedSource
          (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
          R'
          (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)))
          (diagonalImmersion Y ≫ f = 𝟙 _)
          (SupportNormalization (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y f),
        eP.F.mapDerivedCategory.map a.hom ≫
            (s.derive (R := R) (R' := R')).derived.iso.hom.app _ ≫
            R'.R.map
              ((eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
                (DerivedCategory.singleFunctor
                  (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l])
                    (diagonalSurface Y)) 0).map i.hom) =
          eP.singleUnit l (ProjectiveLine Y) ≫ b.hom := by
  dsimp
  intro f R a s
  let G := CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  let R' := canonicalDiagonalRightDerived G
  let M := diagonalCompletedSource l Y
  let N := SheafOfModules.unit
    (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
  let i := completedSupportedCoefficientIso l Y eP eW sΔ
  let q := s.ordinary
  let j : eP.F.obj N ≅ Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)) :=
    eP.unitIso
  let k : eW.F.obj M ≅ source
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y := i
  let ai : N ≅ (diagonalTracePush l f).obj M := a.iso
  let bi : Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)) ≅
      G.obj (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) :=
    j.symm ≪≫ (eP.F.mapIso ai) ≪≫ (q.app M) ≪≫ (G.mapIso k)
  have hbi : eP.F.map a.iso.hom ≫ (q.app M).hom ≫ G.map k.hom =
      j.hom ≫ bi.hom := by
    simp only [bi, j, q, k, ai, Iso.trans_hom, Functor.mapIso_hom]
    simp
  have hc := normalized_transport_core
    (diagonalTracePush l f) G eW.F eP.F R R' s.ordinary (s.derive (R := R) (R' := R')).derived
    a k j bi hbi
  let b : DiagonalTrace.NormalizedSource G R'
      (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
      (Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)))
      (diagonalImmersion Y ≫ f = 𝟙 _)
      (SupportNormalization (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y f) :=
    { over_eq := a.over_eq
      iso := bi
      normalization := by
        exact completedSupportedCoefficient_transport_normalization
          l Y f R a eP eW s i
          (completedSupportedCoefficientIso_normalization l Y eP eW sΔ)
      acyclic := hc.1 }
  refine ⟨b, ?_⟩
  simpa [CompletedRealization.singleUnit, DiagonalTrace.NormalizedSource.hom,
    G, R', k, i, b] using hc.2

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
