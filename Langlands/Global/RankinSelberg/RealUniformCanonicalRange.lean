import Langlands.Global.RankinSelberg.RealExactStandardEvaluation
import Langlands.Global.RankinSelberg.RealLocalEqualGrowthStep
import Langlands.Global.RankinSelberg.RealAscendingWhittakerEvaluation

/-!
# The canonical real Jacquet range and its continuous smooth evaluation

For a real character list, the canonical Jacquet map with parameter `a` has a continuous
Whittaker evaluation for the character `-a` on the genuine smooth standard module, and every
uniform Whittaker coefficient map for `-a` takes its values in the canonical range.
-/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealUniformCanonicalRange

open RealGodement RealGodementProfiles RealPrincipalSeries RealStandardCompactBanach
open RealExactStandardEvaluation (exists_standardEvaluation)
open Langlands.Archimedean.RealJacquetFrobenius (charData)

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

private theorem isCharacterList_characterList {n : ℕ} (p : Fin n → Fin 2) (z : Fin n → ℂ) :
    RealStrictCharacterLanglandsQuotient.IsCharacterList (characterList p z) := by
  intro b hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨c, rfl⟩

/-- The canonical real Jacquet map has a continuous Whittaker evaluation on the genuine smooth
standard module. -/
theorem exists_canonicalStandardEvaluation (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2)
    (z : Fin (r + 1) → ℂ) :
    ∃ L : DerivativeSmoothVectors (matrixModel ℝ (r + 1))
        (RealStandardCompactBanach.representation (n := r + 1) (characterList p z)) →L[ℂ] ℂ,
      IsWhittakerStandardEvaluation (characterList p z) (-a) (canonicalJacquetMap a p z) L :=
  exists_standardEvaluation (r := r) (List.ofFn fun i => charData (p i) (z i)) (-a)
    (canonicalJacquetMap a p z) (realGodementCanonicalModel r a p z).1

theorem realCanonicalStandardEvaluationPremise : RealCanonicalStandardEvaluationPremise :=
  exists_canonicalStandardEvaluation

/-- The canonical coefficients are those of a bounded smooth Whittaker form on the full smooth
position principal series. -/
theorem hasBoundedCanonicalEvaluation (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2)
    (z : Fin (r + 1) → ℂ) : HasBoundedCanonicalEvaluation a p z := by
  obtain ⟨L, hL⟩ := exists_canonicalStandardEvaluation r a p z
  obtain ⟨ℓ, hℓB, hℓψ, hℓ⟩ := exists_boundedForm_of_characterEvaluation (characterList p z)
    (isCharacterList_characterList p z) (-a) L hL.2
  exact ⟨ℓ, hℓB, hℓψ, LinearMap.ext fun f => funext fun g => (hℓ f g).trans (hL.1 f g)⟩

/-- Every uniform Whittaker coefficient of a real character list for the character `-a` is a
canonical coefficient with parameter `a`. -/
theorem uniformWhittakerModel_le_range (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2)
    (z : Fin (r + 1) → ℂ) :
    realUniformWhittakerModel r (characterList p z) (-a) ≤
      LinearMap.range (canonicalJacquetMap a p z) := by
  apply iSup_le
  intro B
  apply iSup_le
  intro hB
  obtain ⟨L, hL⟩ := exists_standardEvaluation (r := r) (List.ofFn fun i => charData (p i) (z i))
    (-a) B hB.1
  obtain ⟨ℓ, hℓB, hℓψ, hℓ⟩ := exists_boundedForm_of_characterEvaluation (characterList p z)
    (isCharacterList_characterList p z) (-a) L hL.2
  obtain ⟨c, hc⟩ := functionalCoefficient_eq_smul_canonical a p z
    (hasBoundedCanonicalEvaluation r a p z) ℓ hℓB hℓψ
  rintro _ ⟨f, rfl⟩
  refine ⟨c • f, ?_⟩
  rw [map_smul]
  funext g
  calc
    (c • canonicalJacquetMap a p z f) g = functionalCoefficient (characterList p z) ℓ f g := by
      rw [hc]
      rfl
    _ = B f g := (hℓ f g).trans (hL.1 f g)

theorem realUniformCanonicalRangePremise : RealUniformCanonicalRangePremise :=
  uniformWhittakerModel_le_range

/-- The two canonical-map premises of the real equal-rank growth step
`RealGodement.realLocalEqualGrowthStep`: every uniform Whittaker coefficient map of a real
character list for `-a` lies in the range of the canonical Jacquet map with parameter `a`, and
every canonical Jacquet map has a continuous Whittaker evaluation on the genuine smooth
standard module. -/
def RealCanonicalRangeAndEvaluationStatement : Prop :=
  RealUniformCanonicalRangePremise ∧ RealCanonicalStandardEvaluationPremise

theorem realCanonicalRangeAndEvaluation : RealCanonicalRangeAndEvaluationStatement :=
  ⟨realUniformCanonicalRangePremise, realCanonicalStandardEvaluationPremise⟩

end Langlands.Global.RankinSelbergGlobal.RealUniformCanonicalRange
