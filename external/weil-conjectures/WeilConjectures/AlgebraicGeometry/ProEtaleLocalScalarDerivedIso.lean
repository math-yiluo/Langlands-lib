/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import all WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import all WeilConjectures.AlgebraicGeometry.PbcActualScalarPullback
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalScalarOrdinaryComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local invariance of derived extension to constant coefficients

Source: Stacks Project, Cohomology on Sites, Tags 06YY, 0G7E and 0E8K.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  proEtaleModuleInverseImage LocalScalar.changeData SheafOfModules.monoidalCategory
  Functor.leftAdjoint
  CochainComplex.IsKFlatIndependentCoefficients CochainComplex.IsKFlatTensor

attribute [local irreducible] LocalScalar.complexCounit LocalScalar.counit

private theorem deriveOrdinarySquare
    {C D A B E : Type*} [Category C] [Category D] [Category A] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A]
    [HasDerivedCategory B] [HasDerivedCategory E]
    (P : ObjectProperty (CochainComplex C ℤ))
    (hres : ∀ K : HomotopyCategory C (.up ℤ),
      ∃ (L : (show ObjectProperty (HomotopyCategory C (.up ℤ)) from
          fun K ↦ P K.as).FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso C (.up ℤ) s)
    (T : C ⥤ D) (H : C ⥤ A) (V : D ⥤ E) (T' : A ⥤ B) (W : B ⥤ E)
    [T.Additive] [H.Additive] [V.Additive] [T'.Additive] [W.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (DT : DerivedCategory C ⥤ DerivedCategory D)
    (DT' : DerivedCategory A ⥤ DerivedCategory B)
    (c : DerivedCategory.Q ⋙ DT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c' : DerivedCategory.Q ⋙ DT' ⟶ T'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hc : ∀ K, P K → IsIso (c.app K))
    (hc' : ∀ K, P K → IsIso (c'.app ((H.mapHomologicalComplex (.up ℤ)).obj K)))
    (b : T ⋙ V ≅ H ⋙ T' ⋙ W) :
    Nonempty (DT ⋙ V.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ DT' ⋙ W.mapDerivedCategory) := by
  let TC := T.mapHomologicalComplex (.up ℤ)
  let HC := H.mapHomologicalComplex (.up ℤ)
  let T'C := T'.mapHomologicalComplex (.up ℤ)
  let dv := V.mapDerivedCategory
  let dw := W.mapDerivedCategory
  let a := Functor.mapHomologicalComplexCompIso (F := T) (G := V) (Iso.refl _) (.up ℤ)
  let a' := Functor.isoWhiskerLeft HC
      (Functor.mapHomologicalComplexCompIso (F := T') (G := W) (Iso.refl _) (.up ℤ)) ≪≫
    Functor.mapHomologicalComplexCompIso (F := H) (G := T' ⋙ W) (Iso.refl _) (.up ℤ)
  let l : DerivedCategory.Q ⋙ (DT ⋙ dv) ⟶
      (T ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight c dv ≫
      Functor.whiskerLeft TC V.mapDerivedCategoryFactors.hom ≫
        (Functor.isoWhiskerRight a DerivedCategory.Q).hom
  let r : DerivedCategory.Q ⋙ (H.mapDerivedCategory ⋙ DT' ⋙ dw) ⟶
      (H ⋙ T' ⋙ W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight H.mapDerivedCategoryFactors.hom (DT' ⋙ dw) ≫
      Functor.whiskerLeft HC (Functor.whiskerRight c' dw) ≫
      Functor.whiskerLeft (HC ⋙ T'C) W.mapDerivedCategoryFactors.hom ≫
        (Functor.isoWhiskerRight a' DerivedCategory.Q).hom
  have hl (K : P.FullSubcategory) : IsIso (l.app K.obj) := by
    have := hc K.obj K.property
    dsimp only [l, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hr (K : P.FullSubcategory) : IsIso (r.app K.obj) := by
    have := hc' K.obj K.property
    dsimp only [r, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨e, _, _⟩ := comparison_on_resolutions P hres _ _ _ _ l r
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex b (.up ℤ)) DerivedCategory.Q) hl hr
  exact ⟨e⟩

private def localRestrictionIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} ((ProEtaleLocalRestriction.inverseRing i R).over U))
    sfbLocalRestriction i R U K ≅ (LocalScalar.restriction i R U).mapDerivedCategory.obj K := by
  let B := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let G := proEtaleRingModulePullback i R B (Iso.refl _)
  let H := proEtaleModuleInverseImage i R
  let T := ProEtaleLocalRestriction.restriction i R U
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} ((ProEtaleLocalRestriction.inverseRing i R).over U))
  let r : SheafOfModules.restrictScalars ((adicLisseForget Y).map (𝟙 B)) ≅
      𝟭 (proEtaleRingModules Y B) :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk
          (fun V ↦ ModuleCat.restrictScalarsId'App _ rfl (M.val.obj V))
          (by intros; ext x; rfl))) (by intros; ext V x; rfl)
  let a := proEtaleRingExtensionAdjunction i R B (Iso.refl _)
  let b := (Adjunction.id (C := proEtaleRingModules Y B)).ofNatIsoRight r.symm
  let e : G ≅ H :=
    Functor.isoWhiskerLeft H (a.leftAdjointUniq b) ≪≫ Functor.rightUnitor H
  let C := DerivedCategory.Q.objPreimage K
  let L := G.mapDerivedCategory.obj K
  let D := DerivedCategory.Q.objPreimage L
  change DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj D) ≅ _
  exact (T.mapDerivedCategoryFactors.app D).symm ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L) ≪≫
    T.mapDerivedCategory.mapIso
      (G.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm) ≪≫
    T.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app C) ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app C)) ≪≫
    T.mapDerivedCategoryFactors.app _ ≪≫
    ((LocalScalar.restriction i R U).mapDerivedCategoryFactors.app C).symm ≪≫
    (LocalScalar.restriction i R U).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso K)

private theorem restrictionKFlat {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt)
    (P : CochainComplex (proEtaleRingModules X R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology X) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U)
      (((LocalScalar.restriction i R U).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists i R
  have : I.modules.Additive := hI.symm ▸ inferInstance
  let F := proEtaleSheafInverseImage i (Type (u + 1))
  let V := proEtaleSheafDirectImage i (Type (u + 1))
  have : RepresentablyFlat (proEtaleBaseChange i) := flat_of_preservesFiniteLimits _
  have : PreservesFiniteLimits F :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage i (𝟙 X)).2.2.2.1
  have hk := SheafOfModules.CanonicalTensorPullbackOfUniverses.isKFlat_inverseImage
    F V (proEtaleSheafAdjunction i (Type (u + 1))) I P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hp) hf
  have he := (NatIso.mapHomologicalComplex (eqToIso hI) (.up ℤ)).app P
  have hk'' : CochainComplex.IsKFlatIndependentCoefficients
      (R := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
      (((proEtaleModuleInverseImage i R).mapHomologicalComplex (.up ℤ)).obj P) :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
    (SheafOfModules.CanonicalTensorPullbackOfUniverses.isKFlat_of_iso
      (R := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) he hk)
  let S := ProEtaleLocalRestriction.restriction i R U
  have hs : CochainComplex.IsKFlatIndependentCoefficients
      (R := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U)
      ((S.mapHomologicalComplex (.up ℤ)).obj
        (((proEtaleModuleInverseImage i R).mapHomologicalComplex (.up ℤ)).obj P)) :=
    (SheafOfModules.ringedSite_restriction_exact_kflat.{u + 1, u, 0}
      (ProEt.topology Y) ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) U).2.2
        _ hk''
  let e := (Functor.mapHomologicalComplexCompIso
    (F := proEtaleModuleInverseImage i R) (G := S) (Iso.refl _) (.up ℤ)).app P
  exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
    (SheafOfModules.CanonicalTensorPullbackOfUniverses.isKFlat_of_iso
      (R := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U) e
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hs))

/-- A local isomorphism over arbitrary ring sheaves induces a local isomorphism after
unbounded derived extension to a constant ring, including its fixed scalar action.
There is no adic, perfectness, boundedness or finiteness assumption.

Source: Stacks Project, Cohomology on Sites, Tags 06YY and 0G7E
(derived pullback and pullback of K-flat complexes), and Tag 0E8K
(restriction of K-flat complexes).
(auxiliary; not a blueprint node).

Proof: let R' and B' be the inverse images of R and the constant ring B.
The module inverse image to R' and restriction to U are exact. Resolve each complex
by a K-flat complex with flat terms. Inverse image and slice restriction preserve
these properties. On these resolutions the canonical tensor comparison identifies
restriction of B tensor_R P with B'|U tensor_(R'|U) restriction(P). It is induced
by inverse image of pure tensors and respects balancing, differentials and the
B action. The K-flat counits identify the corresponding derived functors; their
naturality descends the comparison to the local derived category. Scalar extension
therefore takes the supplied local isomorphism to an isomorphism over B'|U.
The canonical constant-ring inverse-image comparison identifies the scalar B action
with the action on fixed-scalar inverse image, since it carries each constant b to
that same constant b. Forget from modules over B'|U to sheaves of B-modules.
Exactness commutes this operation with localization. The canonical isomorphisms
from localization representatives give exactly the two objects below. The same
argument applies to zero rings, empty slices and unbounded complexes. -/
theorem proEtaleLocalScalarDerivedIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (B : Type (u + 1)) [CommRing B]
    (φ : R ⟶ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of B))
    (U : Y.ProEt) (K K' : DerivedCategory (proEtaleRingModules X R))
    (e : sfbLocalRestriction i R U K ≅ sfbLocalRestriction i R U K') :
    let L := ProEtale.upperStar (ModuleCat.{u + 1} B) i ⋙
      (ProEt.topology Y).overPullback (ModuleCat.{u + 1} B) U
    letI : L.Additive := Functor.additive_of_preserves_binary_products L
    let F := sfbFixedScalarRestriction X B
    let residue := fun M : DerivedCategory (proEtaleRingModules X R) ↦
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        (DerivedCategory.Q.objPreimage ((completedAdicDerivedChange X φ).obj M)))
    Nonempty (L.mapDerivedCategory.obj (residue K) ≅
      L.mapDerivedCategory.obj (residue K')) := by
  let L := ProEtale.upperStar (ModuleCat.{u + 1} B) i ⋙
    (ProEt.topology Y).overPullback (ModuleCat.{u + 1} B) U
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  let F := sfbFixedScalarRestriction X B
  have hF := LocalScalar.fixed_exact (ProEt.topology X) (adicLisseRing X B) B
    (adicLisseConstantUnit X B)
  have : PreservesFiniteLimits F := hF.1
  have : PreservesFiniteColimits F := hF.2
  let H := LocalScalar.restriction i R U
  have hH := LocalScalar.restriction_exact i R U
  have : PreservesFiniteLimits H := hH.1
  have : PreservesFiniteColimits H := hH.2
  let V := F ⋙ L
  let W := LocalScalar.sliceFixed B U
  have hW := LocalScalar.fixed_exact ((ProEt.topology Y).over U)
    ((adicLisseRing Y B).over U) B
    (Functor.whiskerLeft (Over.forget U).op (adicLisseConstantUnit Y B))
  have : PreservesFiniteLimits W := hW.1
  have : PreservesFiniteColimits W := hW.2
  let := LocalScalar.sourceDerived i R U
  let := LocalScalar.targetDerived B U
  let T := completedAdicChange X φ
  let T' := LocalScalar.change i R B φ U
  let : T'.Additive := LocalScalar.change_additive i R B φ U
  let DT := completedAdicDerivedChange X φ
  let DT' : DerivedCategory (LocalScalar.source i R U) ⥤
      DerivedCategory (LocalScalar.target B U) := LocalScalar.derivedChange i R B φ U
  let c := LocalScalar.complexCounit T DT (pbcExtensionCounit φ)
  let c' := LocalScalar.counit i R B φ U
  let P : ObjectProperty (CochainComplex (proEtaleRingModules X R) ℤ) := fun C ↦
    C.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology X) (R := R) (C.X n)
  have hres : ∀ K : HomotopyCategory (proEtaleRingModules X R) (.up ℤ),
      ∃ (M : (show ObjectProperty (HomotopyCategory (proEtaleRingModules X R) (.up ℤ))
          from fun K ↦ P K.as).FullSubcategory) (s : M.obj ⟶ K),
        HomotopyCategory.quasiIso _ (.up ℤ) s := by
    intro K
    obtain ⟨C, f, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K.as
    refine ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj C, hk, ?_⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map f,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (C.X n)).symm (hf n)
  have hc (C) (hp : P C) : IsIso (c.app C) := by
    exact LocalScalar.complexCounit_isIso T DT (pbcExtensionCounit φ) C
      (pbcExtensionCounit_isIso φ C hp.1)
  have hc' (C) (hp : P C) :
      IsIso (c'.app ((H.mapHomologicalComplex (.up ℤ)).obj C)) := by
    exact LocalScalar.counit_isIso i R B φ U
      ((H.mapHomologicalComplex (.up ℤ)).obj C) (restrictionKFlat i R U C hp.1 hp.2)
  obtain ⟨b⟩ := LocalScalar.ordinaryComparison i R B φ U
  obtain ⟨α⟩ := deriveOrdinarySquare P hres T H V T' W DT DT' c c' hc hc' b
  let Dloc := DT' ⋙ W.mapDerivedCategory
  let eH := (localRestrictionIso i R U K).symm ≪≫ e ≪≫ localRestrictionIso i R U K'
  let iso (M : DerivedCategory (proEtaleRingModules X R)) :
      L.mapDerivedCategory.obj (DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage (DT.obj M)))) ≅
        V.mapDerivedCategory.obj (DT.obj M) :=
    L.mapDerivedCategory.mapIso
      ((F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage (DT.obj M))).symm ≪≫
        F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso (DT.obj M))) ≪≫
      (Functor.mapDerivedCategoryCompIso F L).app (DT.obj M)
  exact ⟨iso K ≪≫ α.app K ≪≫ Dloc.mapIso eH ≪≫ (α.app K').symm ≪≫ (iso K').symm⟩

end AlgebraicGeometry.Scheme
