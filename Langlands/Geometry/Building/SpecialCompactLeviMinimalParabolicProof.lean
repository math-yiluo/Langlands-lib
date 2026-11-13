import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof

/-! # Algebraic minimal-parabolic compatibility in actual standard Levi schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The same generic cocharacter defines the minimal parabolic of each actual
standard Levi, with the literal ambient intersection on rational points. -/
theorem standardLeviMinimalParabolicCompatibility :
    StandardLeviMinimalParabolicCompatibilityStatement.{u} := by
  intro F _ _ _ _ G hG S i hi ν
  let := hG.isAffineHom
  intro hν J hJ
  let := hi.isSplitSubtorus.mono
  have hL := Langlands.BruhatTits.SpecialCompact.standardLevi_isConnectedReductive
    hG i hi ν hν J hJ
  let := hL.isAffineHom
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := Langlands.HarishChandraSchwartz.isGenericCocharacter_leviTorusHom
    (J := J) hν
  obtain ⟨-, hcG⟩ := standardCocharacter F G hG S i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨hPG, -, -⟩ := hcG ν (isStandardCocharacter_empty_self i ν)
  refine ⟨hL, ?_, ?_,
    Standard.leviGenericParabolic_eq_comap_standard i ν J hPG,
    Standard.leviGenericParabolic_points_map i ν J hPG⟩
  · rw [hPG]
    exact genericMinimalParabolic F G hG S i hi ν hν
  · exact genericMinimalParabolic F (Standard.leviScheme i ν J) hL S
      (Standard.leviTorusHom i ν J) hiL ν hνL

end Langlands.GroupScheme
