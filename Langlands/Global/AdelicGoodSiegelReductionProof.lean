import Langlands.Global.AdelicSiegelFiniteVolume
import Langlands.Global.AdelicSiegelSetupExistenceProof
import Langlands.Global.AdelicCompatibleIwasawaCompact
import Langlands.Global.InfinitePlaceLeviIwasawaProof
import Langlands.Global.FinitePlaceIwasawaProof
import Langlands.Global.IntegralIwasawaFamilyProof
import Langlands.Global.AdelicSpringerCentralCompactnessProof
import Langlands.Global.AdelicSiegelChamberReduction
import Langlands.Global.AdelicSiegelChamberReductionProof

/-! # Good Siegel reduction for connected reductive groups over number fields: proof

`Langlands.Global.AdelicSiegelFactors.adelicGoodSiegelReduction` proves the Library
proposition `Langlands.Global.AdelicSiegelFactors.AdelicGoodSiegelReductionStatement`, and
`Langlands.Global.AdelicSiegelFactors.adelicSiegelReduction` derives from it the original
`Langlands.Global.AdelicSiegelFactors.AdelicSiegelReductionStatement`.

The proof assembles published proofs: existence of the actual algebraic Siegel setup, a
maximal compact subgroup satisfying the parabolic Iwasawa decomposition and commuting on
its parabolic part with the positive torus (from the archimedean Levi-compatible Iwasawa
theorem, the finite-place parabolic Iwasawa theorem and the almost-everywhere integral
Iwasawa family), Springer's compactness theorem for the minimal Levi modulo its central
split torus, and the chamber form of the fundamental set theorem. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- For every actual algebraic Siegel setup there is a maximal compact subgroup of the
adelic points satisfying the parabolic Iwasawa decomposition for the canonical minimal
parabolic, whose parabolic part commutes with the positive torus. -/
theorem adelicCompatibleIwasawaCompact : AdelicCompatibleIwasawaCompactStatement.{u} :=
  adelicCompatibleIwasawaCompactStatement_of_local
    InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement
    FinitePlaceGroupPoints.parabolicIwasawaStatement
    IntegralIwasawaFamily.existenceStatement

/-- **Good Siegel reduction.** Every affine, locally finite type, connected reductive group
scheme over a number field admits an actual algebraic Siegel setup, compact factors and a
positive threshold satisfying the Siegel cover predicate, whose compact subgroup commutes on
its parabolic part with the positive torus. -/
theorem adelicGoodSiegelReduction : AdelicGoodSiegelReductionStatement.{u} := by
  intro F _ _ G _ _ hG
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence F G hG
  obtain ⟨K, hKI, hKc⟩ := adelicCompatibleIwasawaCompact F G hG T i ν T₀ j hS
  obtain ⟨C, t, hCK, hC⟩ := exists_isSiegelCover_of_chamber centralSplitCompactQuotient
    adelicSiegelChamberReduction F G hG T i ν T₀ j hS K hKI
  subst hCK
  exact ⟨T, i, ν, T₀, j, hS, C, t, hC, hKc⟩

/-- **Siegel reduction.** The original Library Siegel reduction target, obtained from good
Siegel reduction by forgetting the positive-torus compatibility. -/
theorem adelicSiegelReduction : AdelicSiegelReductionStatement.{u} :=
  adelicSiegelReductionStatement_of_good adelicGoodSiegelReduction

end Langlands.Global.AdelicSiegelFactors
