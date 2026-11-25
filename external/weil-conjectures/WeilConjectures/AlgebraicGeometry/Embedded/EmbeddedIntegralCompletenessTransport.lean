/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.Embedded.EmbeddedIntegralScalarKernelSquare
import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement

/-! # Transport of embedded integral coefficients

Source: the integral-models Stacks comparison, Stacks Tag 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem smallModulesEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (IntegralModelsStacks.smallModules X R).IsEquivalence := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)
  let B := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (J := Scheme.ProEt.topology X)
    (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact inferInstanceAs
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor ⋙ e.inverse).IsEquivalence

private theorem completeIso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {O S : Sheaf J CommRingCat.{u + 1}} (q : O ⟶ S)
    {K L : ConstantCompletion.D O} (e : K ≅ L) :
    ConstantCompletion.IsComplete q K ↔ ConstantCompletion.IsComplete q L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod O)
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (O.over U))
  constructor <;> intro h U f hf
  · exact (h U f hf).of_iso ((derivedInternalHom (J.over U) (O.over U)).mapIso
      ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e.symm)))
  · exact (h U f hf).of_iso ((derivedInternalHom (J.over U) (O.over U)).mapIso
      ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e)))

private def smallRestrictionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Mod.comap f ⋙ IntegralModelsStacks.smallModules X R ≅
      IntegralModelsStacks.smallModules X S ⋙
        ConstantCompletion.res (IntegralModelsStacks.smallMap X f) := by
  dsimp only [IntegralModelsStacks.smallModules, IntegralModelsStacks.smallMap]
  let e := CondensedRing.sectionModuleComapIso X f
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      exact (((e.hom.app M).val.app (op (AsSmall.down.obj U.unop))).hom.map_smul r m).symm
    · intro U V g
      ext m
      rfl
  · intro M N g
    ext U m
    rfl

private theorem completeRestriction
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S T U : Sheaf J CommRingCat.{u + 1}}
    (c : S ⟶ R) (qS : S ⟶ T) (qR : R ⟶ U)
    (hk : (ConstantCompletion.kernelIdeal qS).extension c =
      ConstantCompletion.kernelIdeal qR) (N : ConstantCompletion.D R) :
    ConstantCompletion.IsComplete qS ((ConstantCompletion.dres c).obj N) ↔
      ConstantCompletion.IsComplete qR N := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  let (V : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (R.over V))
  let (V : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (S.over V))
  have h := siteDerivedRestrictScalars_locallyDerivedComplete_iff c
    (ConstantCompletion.kernelIdeal qS) N
  rw [hk] at h
  exact h

attribute [local irreducible] IntegralModelsStacks.smallDerivedObject
  IntegralModelsStacks.smallModules IntegralModelsStacks.smallMap
  ConstantCompletion.kernelIdeal RingedSiteIdeal.extension

-- reason for change: coefficient and small-site derived transport
-- elaboration unfolds large equivalences.
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- A continuous coefficient ring isomorphism preserves the local completeness condition.

Source: integral-models-stacks, scalar-square transport; Stacks Tags 0999, 099F and 09C1
(blueprint: lem-sfb-embedded-integral-completeness-transport).

Proof: evaluate e on the one-point profinite set. Naturality for each point of a
profinite S shows that e acts on every continuous function by this ring isomorphism
on its values. In particular it carries constant functions to constant functions.
The induced isomorphism of integer rings carries the unique maximal ideal to the
unique maximal ideal. The hypothesis on pi therefore identifies the kernel of the
first quotient with the kernel of the spectral first quotient. Constant sheafification
and exact inverse image preserve the scalar square. Restriction along the resulting
isomorphisms commutes with restriction along the constant-to-continuous maps.
The section-module equivalence and the equivalent small site preserve this square.
On every slice, corresponding kernel sections have corresponding localizations;
restriction along the ring isomorphism identifies the derived internal Hom from each
localization. It preserves and reflects zero objects. Applying this to every slice and
every kernel section proves the iff, for arbitrary complexes without a bound.
-/
theorem embeddedIntegralCompletenessTransport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)]
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (e : Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.val) ≅
      sfbCondensedIntegers ℓ (ULift.{u} E.val))
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) :
    IntegralModelsEmbedded.constantComplete ℓ E π X
      ((IntegralModelsEmbedded.restriction ℓ E X).obj K) ↔
    ConstantCompletion.IsComplete
      (IntegralModelsStacks.smallMap X
        (IntegralModelsStacks.residueMap ℓ (ULift.{u} E.val) X))
      (IntegralModelsStacks.smallDerivedObject X _
        ((IntegralModelsStacks.restriction ℓ (ULift.{u} E.val) X).obj
          ((Mod.comap ((upperStarFromPoint X).map
            e.inv.hom)).mapDerivedCategory.obj
          K))) := by
  obtain ⟨a, hsquare, hkernel⟩ := embeddedIntegralScalarKernelSquare ℓ E π hπ e X
  let R := condensedRingObj
    (IntegralModelsEmbedded.discreteObj (PadicAlgCl.integers ℓ E.1)) X
  let S := condensedRingObj (IntegralModelsStacks.discreteObj
    (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val))) X
  let φ := IntegralModelsEmbedded.scalarMap ℓ E X
  let ψ := IntegralModelsStacks.scalarMap ℓ (ULift.{u} E.val) X
  let τ := (upperStarFromPoint X).map e.inv.hom
  let qR := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.residueMap ℓ E π X)
  let qS := IntegralModelsStacks.smallMap X
    (IntegralModelsStacks.residueMap ℓ (ULift.{u} E.val) X)
  let c := IntegralModelsStacks.smallMap X a.hom.hom
  let FR := IntegralModelsStacks.smallModules X R
  let FS := IntegralModelsStacks.smallModules X S
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X R))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X S))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard
      (ConstantCompletion.Mod ((IntegralModelsStacks.smallRing X R).over U))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard
      (ConstantCompletion.Mod ((IntegralModelsStacks.smallRing X S).over U))
  have : FR.IsEquivalence := smallModulesEquivalence X R
  have : FS.IsEquivalence := smallModulesEquivalence X S
  have : FR.Additive := Functor.additive_of_preserves_binary_products FR
  have : FS.Additive := Functor.additive_of_preserves_binary_products FS
  have : PreservesFiniteLimits (ConstantCompletion.res c) := (siteRestrictScalars_exact c).1
  have : PreservesFiniteColimits (ConstantCompletion.res c) := (siteRestrictScalars_exact c).2
  let ε : Mod.comap τ ⋙ Mod.comap ψ ≅ Mod.comap φ ⋙ Mod.comap a.hom.hom :=
    (Mod.comapComp ψ τ).symm ≪≫ Mod.comapCongr hsquare.symm ≪≫
      Mod.comapComp a.hom.hom φ
  let α : (Mod.comap τ).mapDerivedCategory ⋙ (Mod.comap ψ).mapDerivedCategory ≅
      (Mod.comap φ).mapDerivedCategory ⋙ (Mod.comap a.hom.hom).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso ε ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  let β : (Mod.comap a.hom.hom).mapDerivedCategory ⋙ FS.mapDerivedCategory ≅
      FR.mapDerivedCategory ⋙ (ConstantCompletion.res c).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (smallRestrictionIso X a.hom.hom) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  let L := (Mod.comap φ).mapDerivedCategory.obj K
  let M := (Mod.comap ψ).mapDerivedCategory.obj ((Mod.comap τ).mapDerivedCategory.obj K)
  let δ : FS.mapDerivedCategory.obj M ≅
      (ConstantCompletion.res c).mapDerivedCategory.obj (FR.mapDerivedCategory.obj L) :=
    FS.mapDerivedCategory.mapIso (α.app K) ≪≫ β.app L
  let ρ : FR.mapDerivedCategory.obj L ≅ IntegralModelsStacks.smallDerivedObject X R L := by
    unfold IntegralModelsStacks.smallDerivedObject
    exact FR.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L).symm ≪≫
      FR.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)
  let σ : FS.mapDerivedCategory.obj M ≅ IntegralModelsStacks.smallDerivedObject X S M := by
    unfold IntegralModelsStacks.smallDerivedObject
    exact FS.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      FS.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)
  have h (N : ConstantCompletion.D (IntegralModelsStacks.smallRing X R)) :=
    completeRestriction c qS qR hkernel N
  change ConstantCompletion.IsComplete qR (IntegralModelsStacks.smallDerivedObject X R L) ↔
    ConstantCompletion.IsComplete qS (IntegralModelsStacks.smallDerivedObject X S M)
  exact (completeIso qR ρ).symm.trans
    ((h _).symm.trans ((completeIso qS δ).symm.trans (completeIso qS σ)))

end AlgebraicGeometry.ProEtale
