/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralChartPullbackComparison
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ExtensionZeroPerfectModelTransport
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Integral local models in scheme chart coordinates

## References

* Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

private theorem datumChartEquivalence {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {S : Scheme.{u}} (U : S.ProEt) :
    ∃ e : DerivedCategory (pbcModules U.left (pbcAdicCompletion U.left d)) ≌
        DerivedCategory (SheafOfModules.{u + 1}
          (((adicLisseForget S).obj (pbcAdicCompletion S d)).over U)),
      Nonempty (d.pull U.hom ⋙ e.functor ≅
        (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
          (pbcAdicCompletion S d) U).mapDerivedCategory) := by
  obtain ⟨q, ⟨hq⟩⟩ := chartDerivedEquivalence U (pbcAdicCompletion S d)
  let c := (adicLisseForget U.left).mapIso (d.integralRingIso U.hom)
  let r := proEtaleScalarEquivalence U.left c
  have : r.functor.Additive := inferInstanceAs
    (SheafOfModules.restrictScalars c.hom).Additive
  let e := r.mapDerivedCategory.trans q
  refine ⟨e, ⟨?_⟩⟩
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (derivedPullbackScalarIso U.hom (pbcAdicCompletion S d)
        (pbcAdicCompletion U.left d) (d.integralRingIso U.hom)) q.functor ≪≫ hq

private theorem localModel_iff {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T S : Scheme.{u}} (g : S ⟶ T) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (P : completedConstantDerived (ModuleCat.{u + 1} A)) :
    Nonempty (integralLocalDerived g (pbcAdicCompletion T d) U K ≅
      integralLocalDerived g (pbcAdicCompletion T d) U
        ((integralConstantDerived T d).obj P)) ↔
    Nonempty ((d.pull (U.hom ≫ g)).obj K ≅
      (integralConstantDerived U.left d).obj P) := by
  let H := (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
    (pbcAdicCompletion S d) U).mapDerivedCategory
  let F := (localScalar d g U).functor.mapDerivedCategory
  obtain ⟨e, ⟨he⟩⟩ := datumChartEquivalence d U
  let cK := (d.pullComp U.hom g).app K
  let cP := (d.pullComp U.hom g).app ((integralConstantDerived T d).obj P)
  let tP := (integralConstantDerivedPullIso d (U.hom ≫ g)).app P
  constructor
  · rintro ⟨h⟩
    let h' := F.preimageIso ((normalizedLocalIso d g U K).symm ≪≫ h ≪≫
      normalizedLocalIso d g U ((integralConstantDerived T d).obj P))
    let h'' := e.functor.preimageIso
      (he.app ((d.pull g).obj K) ≪≫ h' ≪≫
        (he.app ((d.pull g).obj ((integralConstantDerived T d).obj P))).symm)
    exact ⟨cK ≪≫ h'' ≪≫ cP.symm ≪≫ tP⟩
  · rintro ⟨h⟩
    let h' := e.functor.mapIso (cK.symm ≪≫ h ≪≫ tP.symm ≪≫ cP)
    let h'' := (he.app ((d.pull g).obj K)).symm ≪≫ h' ≪≫
      he.app ((d.pull g).obj ((integralConstantDerived T d).obj P))
    exact ⟨normalizedLocalIso d g U K ≪≫ F.mapIso h'' ≪≫
      (normalizedLocalIso d g U ((integralConstantDerived T d).obj P)).symm⟩

/-- Pullback preserves integral stratified perfect models in the datum presentation. -/
theorem integralStratifiedPerfect_pullback {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (hK : IsIntegralStratifiedPerfect Y d K) :
    IsIntegralStratifiedPerfect X d ((d.pull f).obj K) := by
  classical
  obtain ⟨s, hs⟩ := hK
  refine ⟨s.pullback f, fun i ↦ ?_⟩
  obtain ⟨V, hV, hm⟩ := hs i
  let j := pullback.snd (s.immersion i) f
  let g := pullback.fst (s.immersion i) f
  let F := proEtaleBaseChange g
  let hT := (terminalIsTerminal (C := (s.domain i).ProEt)).isTerminalObj F
  let a := hT.from (⊤_ (pullback (s.immersion i) f).ProEt)
  let W := (V.functorPushforward F).pullback a
  have hW : W ∈ ProEt.topology (pullback (s.immersion i) f)
      (⊤_ (pullback (s.immersion i) f).ProEt) :=
    (ProEt.topology _).pullback_stable a
      ((CoverPreserving.of_isContinuous F _ _).cover_preserve hV)
  refine ⟨W, hW, ?_⟩
  intro U b hb
  obtain ⟨Z, z, c, hz, _⟩ := hb
  obtain ⟨P, hP, he⟩ := hm Z z hz
  refine ⟨P, hP, (localModel_iff d j U ((d.pull f).obj K) P).mpr ?_⟩
  obtain ⟨e⟩ := (localModel_iff d (s.immersion i) Z K P).mp he
  let v : U.left ⟶ Z.left := c.left ≫ pullback.fst Z.hom g
  have hc : c.left ≫ pullback.snd Z.hom g = U.hom := by
    have hw := c.w
    change c.left ≫ pullback.snd Z.hom g = U.hom ≫ 𝟙 _ at hw
    simpa only [Category.comp_id] using hw
  have hv : (U.hom ≫ j) ≫ f = v ≫ (Z.hom ≫ s.immersion i) := by
    calc
      _ = U.hom ≫ (pullback.snd (s.immersion i) f ≫ f) := Category.assoc _ _ _
      _ = U.hom ≫ (g ≫ s.immersion i) := by rw [pullback.condition]
      _ = (c.left ≫ pullback.snd Z.hom g) ≫ (g ≫ s.immersion i) := by rw [hc]
      _ = v ≫ (Z.hom ≫ s.immersion i) := by
        simpa only [v, Category.assoc] using congrArg
          (fun h ↦ c.left ≫ h ≫ s.immersion i)
          (pullback.condition (f := Z.hom) (g := g)).symm
  let t : (d.pull (U.hom ≫ j)).obj ((d.pull f).obj K) ≅
      (d.pull v).obj ((d.pull (Z.hom ≫ s.immersion i)).obj K) :=
    ((d.pullComp (U.hom ≫ j) f).app K).symm ≪≫
      eqToIso (congrArg (fun h ↦ (d.pull h).obj K) hv) ≪≫
      (d.pullComp v (Z.hom ≫ s.immersion i)).app K
  exact ⟨t ≪≫ (d.pull v).mapIso e ≪≫
    (integralConstantDerivedPullIso d v).app P⟩

end AlgebraicGeometry.Scheme
