import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.Geometry.Building.ValuationAffineRootSystems
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Cocharacter translations and infinite affine-root fibres for integer valuations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- Evaluate a cocharacter of the actual maximal split torus at a field unit and map
the resulting rational point into its actual centralizer. -/
def cocharacterCentralizerPoint (c : cocharacterLattice B.S) (t : kˣ) :
    rationalPoints B.centralizer.Z :=
  rationalPoints.map B.centralizer.s (CocharacterUniformizer.cocharacterPoints k B.S c t)

/-- Every actual rational character evaluates on this point by the integral pairing. -/
theorem rationalCharacterEval_cocharacterCentralizerPoint
    (c : cocharacterLattice B.S) (t : kˣ) (χ : rationalCharacters B.centralizer.Z) :
    rationalCharacterEval χ (B.cocharacterCentralizerPoint c t) =
      t ^ latticePairing B.S (Cartan.characterRestriction B.centralizer.s χ) c := by
  rw [cocharacterCentralizerPoint, ← rationalCharacterEval_characterRestrict]
  exact CocharacterUniformizer.rationalCharacterEval_cocharacterPoints k B.S
    (Cartan.characterRestriction B.centralizer.s χ) c t

/-- Its positive real character order is the order of the unit times the integral pairing. -/
theorem order_character_cocharacterCentralizerPoint
    (c : cocharacterLattice B.S) (t : kˣ) (χ : rationalCharacters B.centralizer.Z) :
    IntegerValuation.order v (rationalCharacterEval χ (B.cocharacterCentralizerPoint c t)) =
      IntegerValuation.order v t *
        (latticePairing B.S (Cartan.characterRestriction B.centralizer.s χ) c : ℝ) := by
  rw [B.rationalCharacterEval_cocharacterCentralizerPoint]
  simp only [IntegerValuation.order, map_zpow, toAdd_zpow, zsmul_eq_mul, Int.cast_mul]
  push_cast
  ring

/-- V6's negative centralizer translation at an evaluated cocharacter is the
negative-order scalar extension of that same integral cocharacter. -/
theorem translation_cocharacterCentralizerPoint
    (c : cocharacterLattice B.S) (t : kˣ) :
    (B.translation (B.cocharacterCentralizerPoint c t)).toAdd =
      (-IntegerValuation.order v t) ⊗ₜ[ℤ] c := by
  apply B.centralizer.bijective.injective
  apply AddMonoidHom.ext
  intro χ
  change eval B.S (Cartan.characterRestriction B.centralizer.s χ)
      (B.translation (B.cocharacterCentralizerPoint c t)).toAdd =
    eval B.S (Cartan.characterRestriction B.centralizer.s χ)
      ((-IntegerValuation.order v t) ⊗ₜ[ℤ] c)
  rw [IntegerValuation.eval_centralizerTranslation,
    B.order_character_cocharacterCentralizerPoint, eval_tmul, neg_mul]

/-- An actual coroot at a unit of order one gives a centralizer translation of
root value `-2`. -/
theorem exists_centralizer_eval_translation_eq_neg_two
    (t : kˣ) (ht : IntegerValuation.order v t = 1) (a : relativeRoots B.i) :
    ∃ z : rationalPoints B.centralizer.Z, eval B.S a (B.translation z).toAdd = -2 := by
  let x : B.Apartment := Classical.arbitrary B.Apartment
  obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
  have hg1 : g ≠ 1 := fun h =>
    hgtop ((x.isValuation.eq_top_iff a a.property g hg).2 h)
  let := B.isConnectedReductive.smooth
  obtain ⟨p, hp⟩ := (rootRankOneFactorization k G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus a a.property g hg hg1).1.exists
  let c := hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 hg hg1
  have hc : latticePairing B.S a.val c = 2 :=
    (hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 hg hg1).1
  refine ⟨B.cocharacterCentralizerPoint c t, ?_⟩
  rw [B.translation_cocharacterCentralizerPoint, eval_tmul, hc, ht]
  norm_num

/-- One actual normalizer element shifts every affine functional of a given root
derivative by the nonzero constant `2`. -/
theorem exists_conjugateAffineFunctional_eq_add_two
    (t : kˣ) (ht : IntegerValuation.order v t = 1) (a : relativeRoots B.i) :
    ∃ n : normalizerPoints B.i, ∀ ψ : B.Apartment →ᵃ[ℝ] ℝ, ψ.linear = rootForm B.i a →
      B.apartment.conjugateAffineFunctional n ψ =
        ψ + AffineMap.const ℝ B.Apartment 2 := by
  obtain ⟨z, hz⟩ := B.exists_centralizer_eval_translation_eq_neg_two t ht a
  refine ⟨B.centralizer.toNormalizer z, fun ψ hψ => ?_⟩
  ext x
  rw [KPApartmentData.conjugateAffineFunctional_apply, ← map_inv,
    B.isOmegaCompatible.smul_eq_vadd]
  simp only [AffineMap.map_vadd, hψ, rootForm_mk, map_inv, toAdd_inv, map_neg, hz,
    AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply, Function.const_apply, vadd_eq_add]
  ring

/-- Corrected AR4's infinitude clause for the extended affine roots, using only
the explicit order-one-unit witness in addition to the supplied building data. -/
theorem infinite_fiber_extendedAffineRoots
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.apartment.extendedAffineRoots) :
    {θ | θ ∈ B.apartment.extendedAffineRoots ∧ θ.linear = ψ.linear}.Infinite := by
  obtain ⟨t, ht⟩ := hunit
  obtain ⟨a, ha, -⟩ := id hψ
  obtain ⟨n, hn⟩ := B.exists_conjugateAffineFunctional_eq_add_two t ht a
  refine AffineRootSystem.infinite_fiber_of_add_const_mem hψ two_ne_zero fun θ hθ hlin => ?_
  rw [← hn θ (hlin.trans ha)]
  exact B.apartment.conjugateAffineFunctional_mem_extendedAffineRoots n hθ

/-- Corrected AR4's infinitude clause for the ordinary affine roots. -/
theorem infinite_fiber_affineRoots
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    {θ | θ ∈ B.affineRoots ∧ θ.linear = ψ.linear}.Infinite := by
  obtain ⟨t, ht⟩ := hunit
  obtain ⟨a, ha, -⟩ := id hψ
  obtain ⟨n, hn⟩ := B.exists_conjugateAffineFunctional_eq_add_two t ht a
  refine AffineRootSystem.infinite_fiber_of_add_const_mem hψ two_ne_zero fun θ hθ hlin => ?_
  rw [← hn θ (hlin.trans ha)]
  exact B.apartment.conjugateAffineFunctional_mem_affineRoots n hθ

end Langlands.Geometry.Building.IntegerValuationBuildingData
