/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations

/-! # Ordinary completed constant models under the quotient-tower comparison -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem completedScalar_eq (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    adicDatumScalar X
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
        quotientFinite := d.quotientFinite } = CompletedConstantReduction.base X d.ideal := by
  apply limit.hom_ext
  intro n
  exact ((adicDatumScalar_exists X
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }).exists.choose_spec n.unop).trans
    (by simpa only [CompletedConstantReduction.base, Opposite.op_unop] using
      ((CompletedConstantReduction.base_exists X d.ideal).choose_spec.1 n.unop).symm)

private noncomputable def completedModelRoundTrip (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    integralConstantModule X d ⋙ pbcRestrict (pbcCompletedComparison X d).hom ≅
      adicLisseConstantModules X A ⋙
        completedAdicChange X (CompletedConstantReduction.base X d.ideal) := by
  let K := completedKoszulConstant X
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let c := (adicLisseForget X).mapIso (pbcCompletedComparison X d)
  have he : K = adicLisseConstantModules X A ⋙
      completedAdicChange X (CompletedConstantReduction.base X d.ideal) := by
    dsimp only [K, completedKoszulConstant]
    rw [completedScalar_eq]
    rfl
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft K (ProEtale.restrictionRoundTrip c.symm) ≪≫
      Functor.rightUnitor K ≪≫ eqToIso he

private noncomputable def pullbackRefl {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback f R _ (Iso.refl _) ≅ proEtaleModuleInverseImage f R :=
  (proEtaleRingModuleAdjunction f R _ (Iso.refl _)).leftAdjointUniq
    (proEtaleModuleInverseImageAdjunction f R)

private noncomputable def inverseImageRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : R ≅ S) :
    pbcRestrict c.hom ⋙ proEtaleModuleInverseImage f R ≅
      proEtaleModuleInverseImage f S ⋙
        pbcRestrict ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map c.hom) := by
  let a := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map c.hom
  let t := proEtaleRingRestrictionPullbackInv f R S _ _ c.hom a
    (Iso.refl _) (Iso.refl _) (by simp [a])
  have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso f R S _ _ c.hom a
    (Iso.refl _) (Iso.refl _) (by simp [a])
  exact Functor.isoWhiskerLeft (pbcRestrict c.hom) (pullbackRefl f R).symm ≪≫
    asIso t ≪≫ Functor.isoWhiskerRight (pullbackRefl f S) (pbcRestrict a)

private noncomputable def inverseImageSliceRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : R ≅ S) (U : X.ProEt) :
    let cX := (adicLisseForget X).mapIso
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso c)
    let cU := ((ProEt.topology X).overPullback RingCat.{u + 1} U).mapIso cX
    pbcRestrict c.hom ⋙ proEtaleModuleInverseImage f R ⋙
        SheafOfModules.overFunctor _ U ≅
      proEtaleModuleInverseImage f S ⋙ SheafOfModules.overFunctor _ U ⋙
        SheafOfModules.restrictScalars cU.hom := by
  let cX := (adicLisseForget X).mapIso
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso c)
  let t : pbcRestrict
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map c.hom) ⋙
        SheafOfModules.overFunctor _ U ≅
      SheafOfModules.overFunctor _ U ⋙ SheafOfModules.restrictScalars
        (((ProEt.topology X).overPullback RingCat.{u + 1} U).mapIso cX).hom :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ Iso.refl _)))
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (inverseImageRestriction f c) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ t

private theorem localModel_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : R ≅ S) (U : X.ProEt)
    (M N : pbcModules Y S) :
    Nonempty ((SheafOfModules.overFunctor _ U).obj
      ((proEtaleModuleInverseImage f S).obj M) ≅
      (SheafOfModules.overFunctor _ U).obj ((proEtaleModuleInverseImage f S).obj N)) ↔
    Nonempty ((SheafOfModules.overFunctor _ U).obj
      ((proEtaleModuleInverseImage f R).obj ((pbcRestrict c.hom).obj M)) ≅
      (SheafOfModules.overFunctor _ U).obj
        ((proEtaleModuleInverseImage f R).obj ((pbcRestrict c.hom).obj N))) := by
  let cX := (adicLisseForget X).mapIso
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso c)
  let cU := ((ProEt.topology X).overPullback RingCat.{u + 1} U).mapIso cX
  let G := SheafOfModules.restrictScalars.{u + 1} cU.hom
  have : G.IsEquivalence := ProEtale.restriction_isEquivalence cU
  let α := inverseImageSliceRestriction f c U
  constructor
  · rintro ⟨e⟩
    exact ⟨α.app M ≪≫ G.mapIso e ≪≫ (α.app N).symm⟩
  · rintro ⟨e⟩
    exact ⟨G.preimageIso ((α.app M).symm ≪≫ e ≪≫ α.app N)⟩

/-- The two completed-ring presentations give the same finite scalar local models.
This is a statement about ordinary module sheaves, for any adic coefficient datum.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), and the
finite-projection construction of pbcCompletedComparison.
(auxiliary; not a blueprint node).

Proof: restriction along pbcCompletedComparison and its inverse gives inverse
module equivalences. Both round trips are identity on sections. The equivalences
commute with inverse image to each stratum and restriction to each slice, by the
scalar pullback adjunctions and the naturality of the coefficient isomorphism.
By definition integralConstantModule is completedKoszulConstant followed by
restriction along the inverse comparison, so the forward restriction cancels this
last factor. The scalar map adicDatumScalar equals CompletedConstantReduction.base:
all its finite projections are the same quotient maps, and maps into the limit
are determined by these projections. Thus completedKoszulConstant is the ordinary
completedAdicChange realization of the constant module. Apply the slice coefficient
equivalence to every local-model isomorphism, keeping its finitely presented scalar
module and its covering sieve. For the converse apply the inverse equivalence.
A constructible stratification is exactly a finite locally closed stratification
with constructibility proofs for each stratum; forgetting or restoring these
proof fields retains every stratum scheme and immersion. This gives the two
existential witnesses without a change of local models. Empty stratifications and
zero scalar modules satisfy the same argument. -/
theorem completedConstantModelTransport (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : pbcModules X (pbcAdicCompletion X d)) :
    IsIntegralStratifiedFinitelyPresented X d M ↔
      IsCompletedConstantStratified X d.ideal
        ((pbcRestrict (pbcCompletedComparison X d).hom).obj M) := by
  let c := pbcCompletedComparison X d
  let β := completedModelRoundTrip X d
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.toFiniteLocallyClosed, s.isConstructible_stratum, fun i ↦ ?_⟩
    obtain ⟨V, hV, hmodels⟩ := hs i
    refine ⟨V, hV, fun U f hf ↦ ?_⟩
    obtain ⟨N, hN, ⟨ε⟩⟩ := hmodels U f hf
    obtain ⟨ε'⟩ := (localModel_iff (s.immersion i) c U M
      ((integralConstantModule X d).obj N)).mp ⟨ε⟩
    refine ⟨N, hN, ⟨ε' ≪≫ ?_⟩⟩
    exact (SheafOfModules.overFunctor _ U).mapIso
      ((proEtaleModuleInverseImage (s.immersion i) _).mapIso (β.app N))
  · rintro ⟨s, hc, hs⟩
    refine ⟨s.withConstructibleStrata hc, fun i ↦ ?_⟩
    obtain ⟨V, hV, hmodels⟩ := hs i
    refine ⟨V, hV, fun U f hf ↦ ?_⟩
    obtain ⟨N, hN, ⟨ε⟩⟩ := hmodels U f hf
    refine ⟨N, hN, (localModel_iff (s.immersion i) c U M
      ((integralConstantModule X d).obj N)).mpr ⟨ε ≪≫ ?_⟩⟩
    exact (SheafOfModules.overFunctor _ U).mapIso
      ((proEtaleModuleInverseImage (s.immersion i) _).mapIso (β.app N).symm)

end AlgebraicGeometry.Scheme
