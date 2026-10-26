import Langlands.ClassField.Global.IdeleFiniteInvariantRestriction
import Langlands.ClassField.Global.IdeleClassGaloisDescentProof
import Langlands.ClassField.Global.InvariantLocalFromTotal
import Langlands.Global.Arithmetic.CyclicPrimePowerLocalDegreeProof
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.ClassField.Global.IdeleClassH2OrderProof

/-! # Existence of the global invariant maps on idele-class cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.ClassFieldTheory.Local FundamentalClass

universe u

/-- Global invariant maps on actual idele-class cohomology, relative to any local
invariant family satisfying the published class-formation and normalization laws. -/
theorem globalInvariantStatement : GlobalInvariantStatement.{u} := by
  have horder : IdeleClassH2OrderBound.{u, u} := ideleClassH2OrderBound.{u, u}
  have hH1 : IdeleClassH1Vanishing.{u} := ideleClassH1Vanishing.{u}
  have hdesc : IdeleClassGaloisDescent.{u, u} := ideleClassGaloisDescent.{u, u}
  have hlocal : Langlands.Global.CyclicPrimePowerLocalDegreeStatement.{u, u} :=
    Langlands.Global.cyclicPrimePowerLocalDegreeStatement.{u, u}
  have hcompat : GlobalInvariantLocalFromTotalStatement.{u} :=
    globalInvariantLocalFromTotalStatement.{u}
  intro I hCF
  have hImages : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages :=
    fun p _ => (hCF p).1.2.1
  have hInflation : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility :=
    fun p _ => (hCF p).1.2.2.1
  have hRestriction : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeRestriction :=
    fun p _ => (hCF p).1.2.2.2
  let s := totalIdeleInvariantMaps I hImages
  have hker : s.KillsQuotientKernel :=
    totalIdeleInvariantMaps_killsQuotientKernel_of_h1 I hImages hH1 hCF
  have hInf : s.InflationCompatible :=
    totalIdeleInvariantMaps_inflation_of_inflationCompatibility I hInflation hImages
  have hRes : s.RestrictionCompatible :=
    totalIdeleInvariantMaps_restriction_of_localLaws I hRestriction hInflation hImages
  have hcyc : s.CyclicRange :=
    totalIdeleInvariantMaps_cyclicRange I hImages hlocal
  let inv := assembledIdeleClassInvariantMaps s hker hInf hRes hcyc hdesc hH1 horder
  have hi : InvariantImages inv :=
    assembledIdeleClassInvariantMaps_images s hker hInf hRes hcyc hdesc hH1 horder
  have hr : InvariantRestrictionOnClasses inv :=
    assembledIdeleClassInvariantMaps_restriction s hker hInf hRes hcyc hdesc hH1 horder
  have hf : InvariantInflationOnClasses inv :=
    assembledIdeleClassInvariantMaps_inflation s hker hInf hRes hcyc hdesc hH1 horder
  have ha : InvariantTotalAgreement I hImages inv := by
    intro F _ _ E _ _ _ _ wf wi a
    change assembledIdeleClassInvariantMaps s hker hInf hRes hcyc hdesc hH1 horder
      F E (ideleQuotientCohomologyMap F E 2 a) = _
    rw [assembledIdeleClassInvariantMaps_apply_quotient]
    exact DFunLike.congr_fun
      (totalIdeleInvariantMaps_eq_of_inflationCompatibility I hInflation hImages wf wi) a
  exact ⟨inv, (isGlobalInvariant_iff_classes I inv).2
    ⟨hi, hr, hf, hcompat I hImages inv hi hr ha⟩⟩

end Langlands.ClassField.Global
