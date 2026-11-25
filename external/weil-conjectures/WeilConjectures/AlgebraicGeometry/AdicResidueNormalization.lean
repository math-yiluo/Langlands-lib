/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
public import WeilConjectures.AlgebraicGeometry.SfbCompletionNormalization
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import all WeilConjectures.AlgebraicGeometry.SfbCompletionNormalization
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.AlgebraicGeometry.FixedScalarSmallCoordinates
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Finite reduction of normalized completed coefficients

Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] ConstantCompletion.completed
  Functor.mapDerivedCategory HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

private local instance modelSheafify (S : Scheme.{u}) :
    HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance modelLocallyBijective (S : Scheme.{u}) :
    (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

attribute [local instance 50000] modelSheafify modelLocallyBijective fixedSheafify

private local instance standardDerived {C : Type*} [Category C] [Abelian C] :
    HasDerivedCategory C := HasDerivedCategory.standard _

private local instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private noncomputable local instance modelAbelian (S : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1}) :
    Abelian (ConstantCompletion.Mod R) :=
  SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _

private noncomputable local instance fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

attribute [local instance 40000] modelAbelian fixedAbelian standardDerived
  fixedLocallyBijective
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

/-- The inverse mate of a square of right adjoints across equivalences. -/
private def residueExtensionIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D} [F.IsEquivalence] [G.IsEquivalence]
    (a : L ⊣ U) (b : L' ⊣ U') (e : U ⋙ F ≅ G ⋙ U') :
    L ⋙ G ≅ F ⋙ L' := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom))
  let : IsIso α := CategoryTheory.isIso_inverseMate_of_equivalences a b e
  exact (asIso α).symm

/-- Derive an ordinary square of exact functors using the composition comparisons. -/
private def residueDerivedSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : B ⥤ A) (V : D ⥤ C) (F : A ⥤ C) (G : B ⥤ D)
    [U.Additive] [V.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : U ⋙ F ≅ G ⋙ V) :
    U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ V.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso U F ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso G V).symm

/-- Small-site precomposition commutes literally with restriction of scalars. -/
private def residueSiteScalarSquare (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcRestrict φ ⋙ proEtaleModuleToModel ((adicLisseForget X).obj R) ≅
      proEtaleModuleToModel ((adicLisseForget X).obj S) ⋙
        ConstantCompletion.res ((sfbModelRings X).map φ) := Iso.refl _

/-- A commuting coefficient square gives a square of scalar restrictions. -/
private def residueScalarSquare
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S R' S' : Sheaf J CommRingCat.{u + 1}}
    (q : R ⟶ S) (q' : R' ⟶ S') (a : R' ≅ R) (b : S' ≅ S)
    (h : a.hom ≫ q = q' ≫ b.hom) :
    ConstantCompletion.res q ⋙ ConstantCompletion.res a.hom ≅
      ConstantCompletion.res b.hom ⋙ ConstantCompletion.res q' :=
  ConstantCompletion.resCompIso a.hom q (q' ≫ b.hom) h ≪≫
    (ConstantCompletion.resCompIso q' b.hom (q' ≫ b.hom) rfl).symm

/-- Restriction along a coefficient isomorphism has restriction along its inverse as inverse. -/
private theorem residueRestrictionEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (e : R ≅ S) :
    (ConstantCompletion.res e.hom).IsEquivalence := by
  let c := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso e
  let transport := CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars c.hom)
    (SheafOfModules.restrictScalars c.inv)
    (ConstantScalarRestriction.restrictCancelIso J c.inv c.hom c.inv_hom_id).symm
    (ConstantScalarRestriction.restrictCancelIso J c.hom c.inv c.hom_inv_id)
  exact transport.isEquivalence_functor

/-- The two site transports cancel on the underlying module presheaves. -/
private def toModelEquivalence (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :=
  CategoryTheory.Equivalence.mk
    (proEtaleModuleToModel R) (proEtaleModuleFromModel R)
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))

/-- The canonical constant-ring comparison preserves constant scalar sections. -/
private theorem normalization_constants_unit (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (U : coefficientProEtaleSiteModel.{u, u} X) (r : k) :
    ((SfbCompletionNormalization.constants X).app (CommRingCat.of k)).hom.hom.app (op U)
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of k))).app
            (op (AsSmall.down.obj U)) r) =
      (toSheafify (coefficientProEtaleModelTopology.{u, u} X)
        ((Functor.const _).obj (CommRingCat.of k))).app (op U) r := by
  let down : proEtaleSiteModel X ⥤ X.ProEt := AsSmall.down
  have : down.IsDenseSubsite (proEtaleModelTopology X) (ProEt.topology X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsDenseSubsite
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.inducedTopology
        (ProEt.topology X)) (ProEt.topology X))
  have : down.IsCocontinuous (proEtaleModelTopology X) (ProEt.topology X) := inferInstance
  have h := down.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
    (proEtaleModelTopology X) (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of k))
  let t := (SfbCompletionNormalization.constants X).app (CommRingCat.of k)
  have hh : t.inv.hom.app (op U)
      ((toSheafify (coefficientProEtaleModelTopology.{u, u} X)
        ((Functor.const _).obj (CommRingCat.of k))).app (op U) r) =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of k))).app
        (op (AsSmall.down.obj U)) r := by
    have hh' := ConcreteCategory.congr_hom (congr_app h (op U)) r
    dsimp only [t, SfbCompletionNormalization.constants, constantSheaf,
      NatIso.ofComponents, Iso.app, Iso.symm, Functor.comp_obj,
      Functor.whiskerLeft_app] at hh' ⊢
    exact hh'
  rw [← hh]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op U)) t.inv_hom_id) _

attribute [local irreducible] SfbCompletionNormalization.constants

attribute [-instance] ConstantScalarRestriction.ringAbelian ConstantScalarRestriction.fixedAbelian
  ConstantScalarRestriction.ringGrothendieck ConstantScalarRestriction.fixedGrothendieck in
/-- Finite reduction is unchanged by normalizing the completed coefficient presentation.
Source: Stacks Tags 03A0, 03CY and 06YY
(auxiliary; not a blueprint node).

Proof: the limit comparison commutes with the zeroth projections. Its inverse and
that of the constant-ring comparison give a commuting square of coefficient maps.
The constant-ring comparison preserves constant sections by compatibility of
sheafification with small-site precomposition. The fixed-scalar coordinate theorem
therefore identifies normalized finite modules with the functor T in the statement.
Precomposition and scalar restriction give a commuting square of exact right adjoints.
Derive that square and take its inverse mate under the scalar-extension adjunctions;
the horizontal functors are equivalences, so the mate is invertible. This identifies
the two derived scalar extensions. The exact-derived factorization isomorphisms and
Q.objObjPreimageIso then remove the representatives in object and sfbResidueComplex.
The fixed-scalar derived category uses its original smaller localization universe;
only the normalized module category uses the standard localization. The argument
works for every unbounded K. For I=0 the same coefficient isomorphisms apply; for
I=A the finite coefficient rings are zero. No completeness or Noetherianity is used. -/
theorem sfbResidue_normalization
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : @DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)) _ _
      (proEtaleRingModules_hasDerivedCategory X (adicLisseCompletedRing X I))) :
    let T : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) ⥤
        ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology X)
          (A ⧸ I ^ (0 + 1))) :=
      (SfbAdicRestriction.modelEquivalence X
      (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))).inverse ⋙
        (ConstantScalarRestriction.restriction (proEtaleModelTopology X)
          (A ⧸ I ^ (0 + 1))).asEquivalence.inverse
    letI : T.IsEquivalence := by
      have : (SfbAdicRestriction.modelEquivalence X
          (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))).inverse.IsEquivalence :=
        (SfbAdicRestriction.modelEquivalence X
          (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))).isEquivalence_inverse
      have : (ConstantScalarRestriction.restriction (proEtaleModelTopology X)
          (A ⧸ I ^ (0 + 1))).asEquivalence.inverse.IsEquivalence :=
        (ConstantScalarRestriction.restriction (proEtaleModelTopology X)
          (A ⧸ I ^ (0 + 1))).asEquivalence.isEquivalence_inverse
      dsimp only [T]
      infer_instance
    letI : T.Additive := Functor.additive_of_preserves_binary_products T
    letI := HasDerivedCategory.standard
      (ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology X)
        (A ⧸ I ^ (0 + 1))))
    Nonempty ((ConstantCompletion.extend
      (ConstantCompletion.projection (proEtaleModelTopology X) A I 0)).obj
        (SfbCompletionNormalization.object X I K) ≅
      T.mapDerivedCategory.obj (DerivedCategory.Q.obj (sfbResidueComplex X I K))) := by
  let T : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) ⥤
      ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology X)
        (A ⧸ I ^ (0 + 1))) :=
    (SfbAdicRestriction.modelEquivalence X
      (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))).inverse ⋙
    (ConstantScalarRestriction.restriction (proEtaleModelTopology X)
      (A ⧸ I ^ (0 + 1))).asEquivalence.inverse
  have : T.IsEquivalence := by
    have := (SfbAdicRestriction.modelEquivalence X
      (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))).isEquivalence_inverse
    have := (ConstantScalarRestriction.restriction (proEtaleModelTopology X)
      (A ⧸ I ^ (0 + 1))).asEquivalence.isEquivalence_inverse
    dsimp only [T]
    infer_instance
  have : T.Additive := Functor.additive_of_preserves_binary_products T
  let π := limit.π (adicLisseRingSystem X I) (op 0)
  let p := ConstantCompletion.projection (proEtaleModelTopology X) A I 0
  let c := SfbCompletionNormalization.coefficients X I
  let t := (SfbCompletionNormalization.constants X).app
    (CommRingCat.of (A ⧸ I ^ (0 + 1)))
  let TB := proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  let TS := proEtaleModuleToModel
    ((adicLisseForget X).obj (adicLisseConstantRing X (A ⧸ I ^ (0 + 1))))
  let H := sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))
  let HB := TB ⋙ ConstantCompletion.res c.inv
  let HS := H ⋙ T
  have : TB.IsEquivalence := (toModelEquivalence X _).isEquivalence_functor
  have : TS.IsEquivalence := (toModelEquivalence X _).isEquivalence_functor
  have : TB.Additive := Functor.additive_of_preserves_binary_products TB
  have : TS.Additive := Functor.additive_of_preserves_binary_products TS
  have : (ConstantCompletion.res c.inv).IsEquivalence :=
    residueRestrictionEquivalence c.symm
  have : (ConstantCompletion.res t.inv).IsEquivalence :=
    residueRestrictionEquivalence t.symm
  have : HB.IsEquivalence := Functor.isEquivalence_trans TB (ConstantCompletion.res c.inv)
  have : HB.Additive := Functor.additive_of_preserves_binary_products HB
  have : (TS ⋙ ConstantCompletion.res t.inv).IsEquivalence :=
    Functor.isEquivalence_trans TS (ConstantCompletion.res t.inv)
  have ht := normalization_constants_unit X (A ⧸ I ^ (0 + 1))
  obtain ⟨hS₀⟩ := fixed_scalar_small_coordinates X (A ⧸ I ^ (0 + 1)) t ht
  have hS : HS ≅ TS ⋙ ConstantCompletion.res t.inv := hS₀
  have : HS.IsEquivalence := Functor.isEquivalence_of_iso hS.symm
  have : HS.Additive := Functor.additive_of_preserves_binary_products HS
  have : H.IsEquivalence := Functor.isEquivalence_of_comp_right H T
  have hp : c.inv ≫ (sfbModelRings X).map π = p ≫ t.inv := by
    apply (Iso.eq_comp_inv t).mpr
    rw [Category.assoc]
    have h := SfbCompletionNormalization.projection X I 0
    change c.hom ≫ p = (sfbModelRings X).map π ≫ t.hom at h
    rw [← h, Iso.inv_hom_id_assoc]
  let eπ : pbcRestrict π ⋙ HB ≅ HS ⋙ ConstantCompletion.res p :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (residueSiteScalarSquare X π) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft TS
        (residueScalarSquare
          ((sfbModelRings X).map π) p c.symm t.symm hp) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hS.symm (ConstantCompletion.res p)
  let dπ : completedAdicDerivedChange X π ⋙ HS.mapDerivedCategory ≅
      HB.mapDerivedCategory ⋙ ConstantCompletion.extend p :=
    residueExtensionIso
      (pbcDerivedScalarAdjunction π)
      (AlgebraicGeometry.ProEtale.IntegralConstantCompletion.derived_scalar_adjunction p).some
      (residueDerivedSquare
        (pbcRestrict π) (ConstantCompletion.res p) HB HS eπ)
  let M := DerivedCategory.Q.obj
    ((TB.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K))
  let eB : SfbCompletionNormalization.object X I K ≅ HB.mapDerivedCategory.obj K :=
    ((ConstantCompletion.res c.inv).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage M)).symm ≪≫
      (ConstantCompletion.res c.inv).mapDerivedCategory.mapIso
        (DerivedCategory.Q.objObjPreimageIso M) ≪≫
      (ConstantCompletion.res c.inv).mapDerivedCategory.mapIso
        ((TB.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
          TB.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)) ≪≫
      (Functor.mapDerivedCategoryCompIso TB (ConstantCompletion.res c.inv)).app K
  let P := DerivedCategory.Q.objPreimage ((completedAdicDerivedChange X π).obj K)
  let : HasDerivedCategory.{u + 1}
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let eS : T.mapDerivedCategory.{u + 1, u + 2}.obj
      (DerivedCategory.Q.{u + 1}.obj (sfbResidueComplex X I K)) ≅
        HS.mapDerivedCategory.obj ((completedAdicDerivedChange X π).obj K) :=
    T.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.{u + 2, u + 1}.app P).symm ≪≫
      (Functor.mapDerivedCategoryCompIso.{_, _, _, _, _, _, u + 2, u + 1, u + 2}
        H T).app (DerivedCategory.Q.obj P) ≪≫
      HS.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso _)
  exact ⟨(ConstantCompletion.extend p).mapIso eB ≪≫ (dπ.app K).symm ≪≫ eS.symm⟩

end AlgebraicGeometry.Scheme
