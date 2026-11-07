import Langlands.Representation.CuspidalSupport.RationalSummandEndCommutativeStatement
import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeCommutative
import Langlands.Representation.CuspidalSupport.RationalPointCentralCharacter
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-! Renard VI.4.3, Corollary (ii): `End (ind_{⁰G}^G ρ)` is commutative exactly when the
restriction of `π` to `⁰G` is multiplicity-free. The characters of `G(F) ⧸ ⁰G` separate its
points through the rational-character valuation, `G(F)` is second countable, and the generic
results of `NormalSubgroupHeckeCommutative` apply to the open normal subgroup `⁰G`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The characters of `G(F) ⧸ ⁰G` separate its points: if `q ≠ 1`, some rational character
`χ` has `ord χ(q) = n ≠ 0`, and `y ↦ 2^{ord χ(y)}` is a character with value `2ⁿ ≠ 1` at `q`. -/
theorem rationalNormKernelQuotient_exists_character_ne_one
    (q : GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) (hq : q ≠ 1) :
    ∃ ω : (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) →* ℂˣ, ω q ≠ 1 := by
  let f : (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) →*
      Multiplicative (GroupScheme.rationalCharacters G →+ ℤ) :=
    (rationalCharacterValuationImage G).subtype.comp
      (rationalNormKernelQuotientEquiv G).toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (rationalNormKernelQuotientEquiv G).injective
  have hfq : Multiplicative.toAdd (f q) ≠ 0 := fun h0 => hq (hf (by
    rw [map_one]
    exact h0))
  obtain ⟨χ, hχ⟩ := DFunLike.ne_iff.mp hfq
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  refine ⟨{ toFun := fun y => u ^ (Multiplicative.toAdd (f y) χ)
            map_one' := by simp
            map_mul' := fun a b => by simp [zpow_add] }, ?_⟩
  intro h1
  change u ^ (Multiplicative.toAdd (f q) χ) = 1 at h1
  have h2 : (2 : ℂ) ^ (Multiplicative.toAdd (f q) χ) = 1 := by
    have := congrArg Units.val h1
    rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_one] at this
  have h3 : (2 : ℝ) ^ (Multiplicative.toAdd (f q) χ) = 1 := by
    have := congrArg norm h2
    rwa [norm_zpow, norm_one, Complex.norm_two] at this
  exact hχ ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h3)

end

/-- Renard VI.4.3, Corollary (ii). -/
theorem rationalSummandEnd_commutative : RationalSummandEndCommutativeStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  have : SecondCountableTopology (GroupScheme.rationalPoints G) :=
    (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  have : SecondCountableTopology (rationalCommonNormKernel G) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : ρ.representation.IsIrreducible := hρ
  have : π.representation.IsIrreducible := hπ
  have := NormalHecke.countable_quotient_of_isOpen (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G)
  have hj0 : SmoothRep.hom j ≠ 0 := by
    obtain ⟨w, hw⟩ := NormalHecke.exists_ne_zero_of_isIrreducible ρ.representation
    intro h0
    apply hw
    apply hj
    rw [h0, map_zero]
    rfl
  constructor
  · intro hcomm σ hσ
    have : σ.representation.IsIrreducible := hσ
    rw [NormalHecke.rank_le_one_iff_of_equiv (NormalHecke.homLinearEquiv σ _)]
    exact NormalHecke.rank_le_one_of_commute (rationalCommonNormKernel G) ρ
      (isOpen_rationalCommonNormKernel G)
      (Whittaker.MirabolicRigidity.rank_le_aleph0 ρ.representation ρ.isSmooth hρ)
      π.representation hcomm (SmoothRep.hom j) hj0 σ.representation
  · intro hmult α β
    have h1 := hmult ρ hρ
    rw [NormalHecke.rank_le_one_iff_of_equiv (NormalHecke.homLinearEquiv ρ _)] at h1
    exact NormalHecke.commute_of_rank_le_one (rationalCommonNormKernel G) ρ
      (isOpen_rationalCommonNormKernel G) π.representation
      (rationalNormKernelQuotient_exists_character_ne_one G) (SmoothRep.hom j) hj h1 α β

end Langlands.CuspidalSupport
