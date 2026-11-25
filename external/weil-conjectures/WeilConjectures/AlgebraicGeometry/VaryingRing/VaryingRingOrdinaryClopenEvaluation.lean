/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryModuleComposition
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryComparisonNormalization
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryCartesianEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinarySectionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.OrdinarySquareComparison.VaryingRingOrdinarySquarePasting

/-!
# Ordinary coefficient evaluation of the clopen comparison

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tags 09AE and 0F7B.
The evaluation used here first takes an ordinary system component, then makes a
constant tower concentrated in degree zero. Its faithfulness concerns ordinary
system morphisms only (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] ordinaryRealization ordinaryPullComparison ordinaryOpenComparison
  moduleAlpha moduleGComp StrictTower.alpha Functor.leftAdjoint

private theorem ordinaryClopenComparison_factor (n : ℕ) :
    OrdinaryClopenComparison R φ n (ordinaryPullComparison R φ n)
      (ordinaryOpenComparison R φ n) := by
  intro V W S T k r p i _ _ _ _ _ _ h
  have hf : moduleAlpha R φ k r p i h =
      (moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
          moduleSectionArrow R φ k r p i h := by
    delta moduleAlpha moduleSectionArrow
    rfl
  have hh := OrdinarySquareComparison.trans
    (ordinaryPullComparison R φ n V S r) (ordinaryPullComparison R φ n W T p)
    (ordinaryOpenComparison R φ n V W k) (ordinaryOpenComparison R φ n S T i)
    (ordinaryPullComparison R φ n _ S (pullback.snd p i))
    (ordinaryOpenComparison R φ n _ W (pullback.fst p i))
    _ _ _ _
    (ordinaryCartesianEvaluation R φ n (pullback.snd p i)
      (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip)
    (ordinarySectionEvaluation R φ n k r p i h)
  simpa only [hf, strictAlpha_factorization] using hh

/-- Ordinary evaluation preserves the specified inverse-image and open-extension
comparisons and the single-square clopen arrow.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 09AE and 0F7B
(blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation).
Proof: evaluate a system at n, embed the resulting module as a constant tower,
and apply the degree-zero embedding. The inverse-image comparison is moduleEvalG,
whiskered by the constant and single functors and their exact-functor comparisons.
The open comparison is its inverse open-adjunction mate. Evaluation and constant
embedding preserve that mate's unit normalization; exact localization preserves
the same unit, so this mate is invertible. For pullback composition take proper
adjunction mates: moduleEvalP is the identity on section carriers, and the two
pushforward compositors are restriction along the same pullback-pasting map.
Their equality on sections proves pull_comp by injectivity of the mate equivalence.
For open composition transpose once more: moduleJComp and the strict-tower jComp
are both conjugate to these pullback compositors. This proves open_comp.
For clopen, use the chosen pullback W ×_T S. Evaluation keeps the pullback lift
label, so the unit transpose defining moduleBeta evaluates to the strict-tower
beta. The canonical lift is clopen. On its image the projection is the open unit;
on its complement it is zero. Evaluation, constant embedding, and the single
functor keep these two maps. The two-component sheaf decomposition therefore
identifies the evaluated projector with the strict-tower pi. Substitute these
identifications into moduleAlpha and use the two compositor comparisons just
proved. The resulting equation is clopen. This calculation is on ordinary
systems and their degree-zero complexes; it uses no faithfulness of derived
evaluations and assumes no vertical or horizontal pasting law. -/
theorem ordinaryClopenEvaluation (n : ℕ) :
    ∃ (gIso : OrdinaryPullComparison R φ n) (jIso : OrdinaryOpenComparison R φ n),
      OrdinaryPullComposition R φ n gIso ∧ OrdinaryOpenComposition R φ n jIso ∧
        OrdinaryClopenComparison R φ n gIso jIso := by
  have hn := ordinaryComparisonNormalization R φ n
  exact ⟨ordinaryPullComparison R φ n, ordinaryOpenComparison R φ n, hn.1,
    hn.2, ordinaryClopenComparison_factor R φ n⟩

end AlgebraicGeometry.ProEtale.VaryingRing
