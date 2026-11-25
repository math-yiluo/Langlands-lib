/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedLocalPresentationPullback
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation

/-! Restrict a finite coefficient model through the image of an immersion. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStarComp CondensedRing.pullIso
  CondensedRing.upperStarLowerStarAdjunction

/-- A locally finitely presented model over condensed coefficients on an immersed subscheme
induces a locally finitely presented model along every morphism with image in that
subscheme.

Source: `ModuleObject/Colimit/TwoColimit.lean`, open-stratum support step; Stacks
Project Tags 09AA and 09AH.
Proof: form the pullback of the immersion along `g`. Its second projection is a
surjective immersion, hence a closed immersion. Pull the finite model back by the
first projection, then push it forward by the second projection. Local finite
presentation is preserved by these two operations. On the pullback, coefficient
extension commutes with inverse image, the counit identifies the pulled-back
pushforward with the original pulled-back model, and the pullback-square equation
identifies the two restrictions of `M`. The inverse image along the surjective closed
immersion is fully faithful, so this isomorphism lifts to the required scalar-extension
isomorphism on `U`.
(auxiliary; not a blueprint node)
-/
theorem finite_model_on_immersion_range
    (Λ Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [MonObj Ω] [IsCommMonObj Λ] [IsCommMonObj Ω]
    (a : Λ ⟶ Ω) [IsMonHom a] {T V : Scheme.{u}}
    (f : V ⟶ T) [IsImmersion f]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Ω T))
    (P : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
    (hP : IsLocallyFinitelyPresented (condensedRingObj Λ V) P)
    (e : (Mod.extendScalars (coefficientMap a V)).obj P ≅
      (CondensedRing.upperStar Ω f).obj M)
    {U : Scheme.{u}} (g : U ⟶ T) (hr : Set.range g ⊆ Set.range f) :
    ∃ (Q : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)),
      IsLocallyFinitelyPresented (condensedRingObj Λ U) Q ∧
      Nonempty ((Mod.extendScalars (coefficientMap a U)).obj Q ≅
        (CondensedRing.upperStar Ω g).obj M) := by
  obtain ⟨W, p, q, hsq⟩ : ∃ (W : Scheme.{u}) (p : W ⟶ V) (q : W ⟶ U),
      IsPullback p q f g :=
    ⟨pullback f g, pullback.fst _ _, pullback.snd _ _, IsPullback.of_hasPullback _ _⟩
  have : IsImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have hq : Surjective q := by
    refine ⟨fun u ↦ ?_⟩
    obtain ⟨v, hv⟩ := hr ⟨u, rfl⟩
    obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback v u hv
    refine ⟨hsq.isoPullback.inv w, ?_⟩
    change (hsq.isoPullback.inv ≫ q) w = u
    rw [hsq.isoPullback_inv_snd]
    exact hw
  have hqc : IsClosedImmersion q :=
    IsClosedImmersion.of_isPreimmersion q (by
      rw [Set.range_eq_univ.mpr q.surjective]
      exact isClosed_univ)
  let L := (CondensedRing.upperStar Λ p).obj P
  let Q := (CondensedRing.lowerStar Λ q).obj L
  have hL : IsLocallyFinitelyPresented (condensedRingObj Λ _) L :=
    lfp_condensedUpperStar Λ p P hP
  have hQ : IsLocallyFinitelyPresented (condensedRingObj Λ U) Q :=
    lfp_lowerStar_of_surjective_closed Λ q L hL
  have : (CondensedRing.upperStar Λ q).IsEquivalence :=
    condensedSurjectiveClosedPullback_isEquivalence Λ q
  have : (CondensedRing.upperStar Ω q).IsEquivalence :=
    condensedSurjectiveClosedPullback_isEquivalence Ω q
  let c := asIso ((CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app L)
  let eQ : (CondensedRing.upperStar Ω q).obj
      ((Mod.extendScalars (coefficientMap a U)).obj Q) ≅
      (CondensedRing.upperStar Ω q).obj ((CondensedRing.upperStar Ω g).obj M) :=
    ((CondensedRing.pullIso a q).app Q).symm ≪≫
      (Mod.extendScalars (coefficientMap a _)).mapIso c ≪≫
      (CondensedRing.pullIso a p).app P ≪≫
      (CondensedRing.upperStar Ω p).mapIso e ≪≫
      ((CondensedRing.upperStarComp Ω p f).app M).symm ≪≫
      (eqToIso (congrArg (fun h : W ⟶ T ↦
        (CondensedRing.upperStar Ω h).obj M)
          hsq.w)) ≪≫
      (CondensedRing.upperStarComp Ω q g).app M
  exact ⟨Q, hQ, ⟨(CondensedRing.upperStar Ω q).preimageIso eQ⟩⟩

end AlgebraicGeometry.ProEtale
