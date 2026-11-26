import Langlands.Representation.Exponents.UnitaryJacquetVanishingStandardReductionStatement
import Langlands.Representation.Exponents.UnitaryJacquetExponents
import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.SimultaneousStandardConjugation
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Standard testing of unitary Jacquet vanishing -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The unitary Jacquet vanishing test can be restricted to the proper
parabolics and their Levis in any fixed standard family. -/
theorem unitaryJacquetVanishingStandardReduction :
    UnitaryJacquetVanishingStandardReductionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i ν hi hν π
  constructor
  · intro hall _ _ P M U A p l r a hp hl hr hmul ha _ _ hproper
    exact hall P M U A p l r a hp hl hr hmul ha hproper
  · intro hstd P M U A p l r a hp hl hr hmul ha hproper
    obtain ⟨z, hP, hM⟩ :=
      DynamicLeviConjugacy.exists_cocharacter_parabolic_levi
        parabolicDynamic dynamicGeometricUnipotentRadical hG hp hl
    obtain ⟨g, J, _, hζ, hPstd, hMstd, _, _⟩ :=
      exists_simultaneousStandardConjugate_of_dynamicRealization
        smoothMaximalSplitTorusConjugacy hG hi (relativeRootSystem k G hG T i hi)
        hν p l z hP hM
    let e := G.innerIso g
    have hp' := hp.comp_iso e
    have hproper' : ¬ IsIso (p ≫ e.hom) :=
      fun h => hproper ((isIso_comp_right_iff p e.hom).mp h)
    have hvanish := hstd J hζ.subset P M U A (p ≫ e.hom) l r a
      hp' hl hr hmul ha hPstd hMstd hproper'
    apply (unitaryJacquetPart_eq_bot_iff p l r hp hl hr hmul ha π).mpr
    intro χ hχ
    have hχstd :=
      (isNormalizedJacquetExponent_comp_innerIso_iff p l r hp hl hr hmul ha g π χ).mpr hχ
    exact (unitaryJacquetPart_eq_bot_iff (p ≫ e.hom) l r hp' hl hr hmul ha π).mp
      hvanish χ hχstd

end Langlands.Aubert.General.RepresentedParabolic
