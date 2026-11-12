import Langlands.Representation.Exponents.LeviParabolicExtensionStatement
import Langlands.Representation.Exponents.LeviParabolicTransitivityStatement
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps

/-! # Supercuspidality of the Jacquet module at a minimal parabolic

Renard VI.2.1, Corollary and proof (printed p.139 / PDF p.145): if `P = MU` is minimal
among the parabolics with `r_P^G(π) ≠ 0`, then `r_P^G(π)` is supercuspidal, since a
proper parabolic `P'` of `M` with `r_{P'}^M(r_P^G(π)) ≠ 0` gives a strictly smaller
parabolic of `G` with nonzero Jacquet module, by transitivity of Jacquet functors.

This module proves that step for actual represented parabolics, conditionally on two
published propositions taken as hypotheses: the parabolic extension
`LeviParabolicExtensionStatement`, which produces the parabolic `R` of `G` with Levi `M'`
from a parabolic `P'` of `M`, and the represented transitivity
`LeviParabolicTransitivityStatement`, which identifies `r_R^G` with `r_{P'}^M ∘ r_P^G`.
Minimality is measured by the all-test range of the parabolic in `G`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.2.1, proof, descent step, conditional on parabolic extension and represented
transitivity: let `P = MU` be an actual parabolic datum such that every actual parabolic
datum whose parabolic has strictly smaller all-test range has zero Jacquet module of `π`.
Then the Jacquet module `r_P^G(π)` is supercuspidal: its normalized Jacquet module for
every proper actual parabolic `P'` of `M` is zero. -/
theorem leviJacquet_supercuspidal_of_minimal
    (hExt : LeviParabolicExtensionStatement.{u})
    (hTrans : LeviParabolicTransitivityStatement.{u, v}) :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
        (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        (∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
          (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
          (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
          (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
          (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
          SubgroupFunctor.range p₁ < SubgroupFunctor.range p →
            Subsingleton ((leviJacquetFunctor.{u, v} p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj π)) →
        haveI := hl.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : LocallyCompactSpace (rationalPoints M) :=
          leviPoints_locallyCompactSpace p l hp hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' →
            Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj
              ((leviJacquetFunctor.{u, v} p l r hp hr hl hmul).obj π)) := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π P M U p l r hp hl hr hmul hmin
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro P' M' U' p' l' r' hp' hl' hr' hmul' hne
  by_contra hsub
  have hJ := not_subsingleton_iff_nontrivial.mp hsub
  -- The ambient parabolic `R = M' ⋉ W` of `G` extending `P' ⊂ M`.
  obtain ⟨R, W, pR, nR, rR, hpR, hnR, hrR, hmulR, hcomp, hle, hinf⟩ :=
    hExt k G hG P M U p l r hp hl hr hmul P' M' U' p' l' r' hp' hl' hr' hmul'
  -- The three point-level conditions of transitivity, at the identity test scheme.
  have h₁ : pointImage pR ≤ pointImage p := by
    rw [pointImage_eq_range_carrier pR, pointImage_eq_range_carrier p]
    exact hle _
  have h₃ : pointImage (p' ≫ l ≫ p) = pointImage (l ≫ p) ⊓ pointImage pR := by
    rw [pointImage_eq_range_carrier (p' ≫ l ≫ p), pointImage_eq_range_carrier (l ≫ p),
      pointImage_eq_range_carrier pR, hinf]
    rfl
  obtain ⟨-, ⟨e⟩⟩ := hTrans k G hG R M' W P M U P' U' pR nR rR hpR hnR hrR hmulR
    p l r hp hl hr hmul p' l' r' hp' hl' hr' hmul' h₁ hcomp.symm h₃
  -- `r_R^G(π) ≅ r_{P'}^M(r_P^G(π))` is nonzero, so minimality forces equal ranges.
  let : TopologicalSpace (rationalPoints M') := leviPointTopology nR hnR
  have hR : Nontrivial ((leviJacquetFunctor.{u, v} pR nR rR hpR hrR hnR hmulR).obj π) :=
    @Equiv.nontrivial _ _ (SmoothRep.equivOfIso (e.app π)).toLinearEquiv.toEquiv hJ
  have hnlt : ¬ SubgroupFunctor.range pR < SubgroupFunctor.range p := fun hlt =>
    not_subsingleton_iff_nontrivial.mpr hR (hmin R M' W pR nR rR hpR hnR hrR hmulR hlt)
  have heq : SubgroupFunctor.range pR = SubgroupFunctor.range p :=
    (lt_or_eq_of_le hle).resolve_left hnlt
  -- Then `P'` has the whole range of `M`, so it is not proper.
  have hlp : SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range p :=
    SubgroupFunctor.range_le_of_factor l rfl
  have hrange : SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (p' ≫ l ≫ p) := by
    rw [hinf, heq]
    intro T x hx
    exact Subgroup.mem_inf.mpr ⟨hx, hlp T hx⟩
  exact hne (IsClosedSubgroup.isIso_of_range_le_range_comp hp'.isClosedSubgroup
    (hl.isClosedSubgroup.comp hp.isClosedSubgroup) hrange)

end Langlands.Aubert.General.RepresentedParabolic
