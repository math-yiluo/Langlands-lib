import Langlands.Representation.CuspidalSupport.InducedProgeneratorCenterInclusionStatement
import Langlands.Representation.CuspidalSupport.InducedCenterFactorization
import Langlands.Representation.CuspidalSupport.InducedKernelVanishing
import Langlands.Representation.CuspidalSupport.RationalSummandInductionSupercuspidal

/-! # The centre of `R_Ω` lies in the centre of `R_D` (Renard VI.10.4, second Lemma): proof -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.4, second Lemma: the centre of `End(i_P^G Π_D)` is the set of `i_P^G(z)`,
`z` central in `End(Π_D)`, that commute with `End(i_P^G Π_D)`. -/
theorem inducedProgeneratorCenterInclusion :
    InducedProgeneratorCenterInclusionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π _ hπ ρ₀ _ j hj piD I
  -- `Π_D` is supercuspidal.
  have hsc : IsSupercuspidal piD :=
    isSupercuspidal_rationalNormKernelSummandInduction π hπ ρ₀ j hj
  -- No `t` whose positive powers avoid `⁰M(F)` fixes a nonzero vector of `Π_D`.
  have hfix : ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : piD, piD.representation t v = v → v = 0 := by
    intro t ht v hv
    exact Induction.compactInduced_eq_zero_of_fixed (Plancherel.rationalCommonNormKernel M)
      (Plancherel.isOpen_rationalCommonNormKernel M) _ t ht v hv
  -- Frobenius reciprocity reduces the claim to the kernel vanishing below.
  apply inducedCenter_eq_of_kernelVanishing.{u, v} k G hG P M N p l r hp hl hr hmul piD
  intro h hh f hf
  -- Maps `r_P(i_P Π_D) → Π_D` commuting with `End(Π_D)` vanish off the identity coset.
  -- The arguments are supplied one at a time, with the parabolic data explicit: elaborating
  -- the whole application at once times out.
  have hvan₁ := leviJacquetInduction_hom_apply_mk_eq_zero (p := p) (l := l) (r := r)
    (hp := hp) (hr := hr) (hl := hl) (hmul := hmul) hG piD
  have hvan₂ := hvan₁ hsc
  have hvan₃ := hvan₂ hfix
  have hvan₄ := hvan₃ h
  have hvan₅ := hvan₄ (by intro a y; exact hh a y)
  have hvan₆ := hvan₅ f hf
  exact hvan₆

end Langlands.Aubert.General.RepresentedParabolic
