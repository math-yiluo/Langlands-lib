import Langlands.Representation.Plancherel.RationalUnramifiedDensity
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Nonvanishing of actual regular functions at unitary unramified parameters -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u v

/-- The circle gives infinitely many distinct complex units. -/
theorem infinite_range_circleToUnits : (Set.range Circle.toUnits).Infinite := by
  have hI : (Set.Ioc (-Real.pi) Real.pi).Infinite :=
    Set.Ioc_infinite (by linarith [Real.pi_pos])
  let := hI.to_subtype
  have : Infinite Circle := by
    exact Infinite.of_injective Circle.argEquiv.symm Circle.argEquiv.symm.injective
  exact Set.infinite_range_of_injective (fun x y h =>
    Circle.coe_injective (congrArg Units.val h))

/-- A Laurent polynomial vanishing on every unitary tuple is zero. -/
theorem finiteLaurent_eq_zero_of_eval_unitary {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ))
    (hp : ∀ z : Fin n → Circle,
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p = 0) :
    p = 0 := by
  apply finiteLaurent_eq_zero_of_eval_on_box n
    (fun _ => Set.range Circle.toUnits) (fun _ => infinite_range_circleToUnits) p
  intro c hc
  choose z hz using fun i => hc i (Set.mem_univ i)
  have he : c = fun i => Circle.toUnits (z i) := funext fun i => (hz i).symm
  rw [he]
  exact hp z

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Restrict the actual scalar algebra to the unitary unramified subgroup. -/
def rationalUnitaryRegularRestriction :
    unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul) →ₐ[ℂ]
      (unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) → ℂ) where
  toFun b χ := b.val ⟨χ.val, χ.property.1⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Canonical unitary reconstruction evaluates the actual regular algebra by
the same Laurent polynomials in circle coordinates. -/
theorem rationalUnramifiedLaurentAlgebraEquiv_eval_unitary
    (hG : GroupScheme.IsConnectedReductive G)
    (p : AddMonoidAlgebra ℂ (Fin (rationalImageRank G) → ℤ))
    (z : Fin (rationalImageRank G) → Circle) :
    rationalUnitaryRegularRestriction G
      (rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG p)
      ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm z) =
        finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p := by
  let χ := (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm z
  have hcoord : rationalCanonicalUnramifiedCharacterCoordinates G hG
      ⟨χ.val, χ.property.1⟩ = fun i => Circle.toUnits (z i) := by
    funext i
    apply Units.ext
    rw [← rationalCanonicalUnitaryUnramifiedCharacterCoordinates_coe G hG χ i]
    change (((rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG)
      ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm z) i : Circle) :
        ℂ) = (z i : ℂ)
    rw [ContinuousMulEquiv.apply_symm_apply]
  have he := rationalUnramifiedLaurentAlgebraEquiv_eval G
    (continuous_rationalValuationImageProjection G) hG p ⟨χ.val, χ.property.1⟩
  change rationalUnitaryRegularRestriction G
    (rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG p) χ =
      finiteLaurentEvaluation
        (rationalCanonicalUnramifiedCharacterCoordinates G hG ⟨χ.val, χ.property.1⟩) p at he
  exact he.trans (congrArg (fun c => finiteLaurentEvaluation c p) hcoord)

/-- Vanishing on all unitary unramified characters forces an actual regular
function to be zero. -/
theorem rationalUnramifiedRegular_eq_zero_of_unitary
    (hG : GroupScheme.IsConnectedReductive G)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : ∀ χ, rationalUnitaryRegularRestriction G b χ = 0) :
    b = 0 := by
  let a := rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG
  apply a.symm.injective
  rw [map_zero]
  apply finiteLaurent_eq_zero_of_eval_unitary
  intro z
  rw [← rationalUnramifiedLaurentAlgebraEquiv_eval_unitary G hG (a.symm b) z]
  change rationalUnitaryRegularRestriction G (a (a.symm b)) _ = 0
  rw [a.apply_symm_apply]
  exact hb _

include G in
/-- Restriction to the unitary unramified subgroup is faithful. -/
theorem rationalUnitaryRegularRestriction_injective
    (hG : GroupScheme.IsConnectedReductive G) :
    Function.Injective (rationalUnitaryRegularRestriction G) := by
  intro b c hbc
  apply sub_eq_zero.mp
  apply rationalUnramifiedRegular_eq_zero_of_unitary G hG
  intro χ
  change (rationalUnitaryRegularRestriction G (b - c)) χ = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hbc χ)

/-- Every nonzero actual regular function is nonzero at some unitary parameter. -/
theorem rationalUnramifiedRegular_exists_unitary_ne_zero
    (hG : GroupScheme.IsConnectedReductive G)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) :
    ∃ χ, rationalUnitaryRegularRestriction G b χ ≠ 0 := by
  by_contra h
  apply hb
  apply rationalUnramifiedRegular_eq_zero_of_unitary G hG
  simpa only [not_exists, not_not] using h

/-- Finitely many nonzero actual regular equations can be avoided simultaneously
by one unitary unramified character. -/
theorem rationalUnramifiedRegular_exists_unitary_finset_ne_zero
    (hG : GroupScheme.IsConnectedReductive G)
    {J : Type v} (s : Finset J)
    (b : J → unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : ∀ j ∈ s, b j ≠ 0) :
    ∃ χ, ∀ j ∈ s, rationalUnitaryRegularRestriction G (b j) χ ≠ 0 := by
  classical
  let := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid G
    (continuous_rationalValuationImageProjection G) hG
  obtain ⟨χ, hχ⟩ := rationalUnramifiedRegular_exists_unitary_ne_zero G hG
    (∏ j ∈ s, b j) (Finset.prod_ne_zero_iff.mpr hb)
  refine ⟨χ, ?_⟩
  change (rationalUnitaryRegularRestriction G (∏ j ∈ s, b j)) χ ≠ 0 at hχ
  simpa only [map_prod, Finset.prod_apply, Finset.prod_ne_zero_iff] using hχ

end Actual

end Langlands.Plancherel
