import Langlands.Representation.Conductor.OrderedUnramifiedNondegeneracy
import Langlands.Representation.Conductor.OrderedUnramifiedTopLine
import Langlands.Representation.Conductor.OrderedUnramifiedTransport
import Langlands.Representation.Conductor.OrderedUnramifiedWhittakerReduction
import Langlands.Representation.Conductor.UnramifiedSphericalWhittaker

/-!
# Assembly of the normalized inverse Whittaker realization

The unramified principal series `I(z)` is equivalent to the normalized product of the
rank-one unramified blocks. Transport along this equivalence turns the mirabolic
nondegeneracy of the product (Bernstein–Zelevinsky 4.11) into nonzero inverse-character
coinvariants of every nonzero subrepresentation of `I(z)`, and the one-dimensionality of
the standard coinvariants of the product into one-dimensionality of the inverse-character
coinvariants of `I(z)`. Together with the spherical comparison, the reduction
`realization_of_inputs` gives the realization.
-/

noncomputable section

namespace Langlands.Conductor.OrderedUnramifiedWhittakerAssembly

open Langlands.GeneralLinear Langlands.Jacquet.Localization Langlands.Whittaker
open Langlands.HarmonicAnalysis
open Langlands.Conductor.UnramifiedPrincipalSeries
open Langlands.Conductor.OrderedUnramifiedProductComparison
open Langlands.Conductor.OrderedUnramifiedRankOneBlocks
open Langlands.Conductor.OrderedUnramifiedNondegeneracy
open Langlands.Conductor.OrderedUnramifiedTransport
open Langlands.Conductor.OrderedUnramifiedWhittakerReduction

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : Fˣ}
  (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n : ℕ) {q : ℕ}
  (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)

omit [IsNonarchimedeanLocalField F] in
include hϖ in
/-- A character with integer conductor is nontrivial on `ϖ⁻¹ O`. -/
theorem exists_ne_one_of_hasIntegerConductor {ψ : UnitaryAdditiveCharacter F}
    (hψ : HasIntegerConductor ψ) : ∃ x : F, ψ x ≠ 1 := by
  by_contra h
  push Not at h
  have hmem := hψ.2 ((ϖ : F)⁻¹) (fun y _ => h _)
  rw [Valuation.mem_integer_iff, map_inv₀] at hmem
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ϖ.ne_zero)
  exact absurd hϖ.1 (not_lt.mpr ((inv_le_one₀ hpos).mp hmem))

include hϖ in
/-- The character `x ↦ ψ(-x)` of a character with integer conductor is nontrivial. -/
theorem exists_scale_neg_one_ne_one {ψ : UnitaryAdditiveCharacter F}
    (hψ : HasIntegerConductor ψ) : ∃ x : F, ψ.scale (-1) x ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_ne_one_of_hasIntegerConductor hϖ hψ
  refine ⟨-x, ?_⟩
  rwa [UnitaryAdditiveCharacter.scale_apply, Units.val_neg, Units.val_one, neg_one_mul, neg_neg]

/-- The unramified principal series is equivalent to the normalized product of the
rank-one unramified blocks. -/
def productEquiv :
    letI := (data F).topology
    (principalSeries hϖ n hq z).Equiv (product hϖ n z).representation :=
  principalSeriesEquiv hϖ n hq z (fun i => (rankOneBlock (F := F) hϖ (z i)).obj)
    (lineEquiv (fun _ => ULift.moduleEquiv))
    (fun i g v => rankOneBlock_apply (F := F) hϖ (z i) g v)

/-- Every nonzero subrepresentation of the ordered unramified principal series has nonzero
inverse-character coinvariants, given Bernstein–Zelevinsky's Theorem 4.11. -/
theorem nontrivial_inverseCoinvariants
    (h411 : AllFieldBZ.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF, uF}
      (pkg F) (data F))
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) (ψ : UnitaryAdditiveCharacter F)
    (K : Subrepresentation (principalSeries hϖ n hq z)) (hK : K ≠ ⊥) :
    Nontrivial (InverseCoinvariants n ψ K.toRepresentation) := by
  rw [InverseCoinvariants, ← standardCharacter_scale_neg_one]
  exact nontrivial_coinvariants_of_equiv (productEquiv hϖ n hq z)
    (standardCharacter (ψ.scale (-1)) n) (nontrivial_coinvariants hϖ h411 n z hz (ψ.scale (-1)))
    K hK

/-- The inverse-character coinvariants of the unramified principal series are a line when
the standard coinvariants for `x ↦ ψ(-x)` of the product of rank-one blocks are. -/
theorem finrank_inverseCoinvariants (ψ : UnitaryAdditiveCharacter F)
    (htop : letI := (data F).topology
      Module.finrank ℂ (Coinvariants (product hϖ n z).representation
        (upperUnipotent (n + 1) (pkg F).Carrier) (standardCharacter (ψ.scale (-1)) n)) = 1) :
    Module.finrank ℂ (InverseCoinvariants n ψ (principalSeries hϖ n hq z)) = 1 := by
  rw [standardCharacter_scale_neg_one] at htop
  exact (coinvariantsEquiv (productEquiv hϖ n hq z) (inverseStandardCharacter ψ n)).finrank_eq.trans
    htop

/-- The normalized inverse Whittaker realization, conditional on Bernstein–Zelevinsky's
Theorem 4.11 and on the top line of the product of rank-one blocks. -/
theorem realization_of_product_inputs
    (h411 : AllFieldBZ.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF, uF}
      (pkg F) (data F))
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) (ψ : UnitaryAdditiveCharacter F)
    (hψ : HasIntegerConductor ψ)
    (htop : letI := (data F).topology
      Module.finrank ℂ (Coinvariants (product hϖ n z).representation
        (upperUnipotent (n + 1) (pkg F).Carrier) (standardCharacter (ψ.scale (-1)) n)) = 1) :
    ∃ ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z),
      ℓ.val ≠ 0 ∧
      Function.Injective (coefficientMap (principalSeries hϖ n hq z) ℓ) ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F,
        (coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val g =
          Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z g :=
  realization_of_inputs hϖ n hq z ψ (finrank_inverseCoinvariants hϖ n hq z ψ htop)
    (nontrivial_inverseCoinvariants hϖ n hq z h411 hz ψ)
    (fun ℓ g => coefficientMap_sphericalSection_apply hϖ n hq z hψ ℓ g)

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The realization statement, conditional on Bernstein–Zelevinsky's Theorem 4.11 for every
local-field package and on the top line of the product of rank-one blocks for every
nontrivial additive character. -/
theorem realization_of_h411_htop
    (h411 : ∀ (P : AllFieldBZ.LocalFieldPackage.{uF}) (T : P.TopologicalData),
      AllFieldBZ.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF, uF} P T)
    (htop : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (ϖ : Fˣ)
      (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n : ℕ)
      (z : Fin (n + 1) → ℂˣ) (ψ' : UnitaryAdditiveCharacter F),
      letI := (data F).topology
      Module.finrank ℂ (Coinvariants (product hϖ n z).representation
        (upperUnipotent (n + 1) (pkg F).Carrier) (standardCharacter ψ' n)) = 1) :
    OrderedUnramifiedWhittakerRealizationStatement.{uF} := by
  intro F _ _ _ _ ϖ hϖ n q hq z hz ψ hψ
  exact realization_of_product_inputs hϖ n hq z (h411 (pkg F) (data F)) hz ψ hψ
    (htop F ϖ hϖ n z (ψ.scale (-1)))

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The realization statement, conditional only on Bernstein–Zelevinsky's Theorem 4.11 for
every local-field package. The top line of the product of rank-one blocks is
`OrderedUnramifiedTopLine.finrank_productCoinvariants`. -/
theorem realization_of_h411
    (h411 : ∀ (P : AllFieldBZ.LocalFieldPackage.{uF}) (T : P.TopologicalData),
      AllFieldBZ.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF, uF} P T) :
    OrderedUnramifiedWhittakerRealizationStatement.{uF} := by
  refine realization_of_h411_htop h411 ?_
  intro F _ _ _ _ ϖ hϖ n z ψ'
  exact OrderedUnramifiedTopLine.finrank_productCoinvariants hϖ n z ψ'

end Langlands.Conductor.OrderedUnramifiedWhittakerAssembly
