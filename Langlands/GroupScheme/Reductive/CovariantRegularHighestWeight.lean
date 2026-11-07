import Langlands.GroupScheme.Reductive.CovariantRegularWeights

/-! # The highest-weight line of an actual covariant regular representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

namespace Langlands.GroupScheme.SplitPinning

open AffineCoordinates AffineLinearEmbedding Chevalley MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom
local instance : IsAffine p.positiveUnipotent.X.left :=
  isAffine_of_isAffineHom p.positiveUnipotent.X.hom

variable (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
    (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
      ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
        w ∈ V → rightAct ψ w ∈ V)

/-- Restriction sends the highest-character space of a covariant regular
subspace into the constant coordinates of the positive unipotent subgroup. -/
def covariantHighestRestriction
    {lam : characterLattice p.torus}
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam)) :
    p.representationWeightSpace (affineRegularRepresentation G V b hV) lam →ₗ[k]
      LinearMap.range (Algebra.linearMap k (CharacterUnits.Coord p.positiveUnipotent)) := by
  let W := p.representationWeightSpace (affineRegularRepresentation G V b hV) lam
  let Q := CharacterUnits.Coord p.positiveUnipotent
  let R := p.covariantRegularRestriction V b
  have hR (v : W) : R v ∈ LinearMap.range (Algebra.linearMap k Q) := by
    rw [← p.weightSpace_zero_positiveUnipotentAction]
    simpa only [sub_self] using
      p.covariantRegularRestriction_mem_weightSpace V b hV hcov v.property
  exact (R.comp W.subtype).codRestrict _ hR

/-- The left character space of a covariant regular subspace has dimension at
most one, since restriction embeds it into the constant coordinates. -/
theorem affineRegularRepresentation_highest_finrank_le_one
    {lam : characterLattice p.torus}
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam)) :
    Module.finrank k (p.representationWeightSpace
      (affineRegularRepresentation G V b hV) lam) ≤ 1 := by
  let Q := CharacterUnits.Coord p.positiveUnipotent
  let L := p.covariantHighestRestriction V b hV hcov
  have hi : Function.Injective L := by
    intro v w he
    apply Subtype.ext
    exact p.covariantRegularRestriction_injective V b hcov (congrArg Subtype.val he)
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hconst := LinearMap.finrank_range_le (Algebra.linearMap k Q)
  exact hdim.trans (by simpa only [Module.finrank_self] using hconst)

/-- A weight vector with nonzero counit has the same character as the supplied
left covariance. -/
theorem affineRegularRepresentation_weight_eq_of_counit_ne_zero
    {lam mu : characterLattice p.torus}
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam))
    {v : Fin d → k}
    (hv : v ∈ p.representationWeightSpace (affineRegularRepresentation G V b hV) mu)
    (hv0 : counit (corepresentation G) (affineRegularCoordinateMap G V b v) ≠ 0) :
    mu = lam := by
  apply (rationalCharacters.equivCharacterLattice p.torus).symm.injective
  apply rationalCharacters.ext_characterEval
  intro T s
  apply Units.ext
  have hl := p.pointAlgebraHom_leftTorus_of_covariant
    (hcov (affineRegularCoordinateMap_mem G V b v)) T s 1
  have hr := pointAlgebraHom_affineRegularCoordinateMap_mul_of_character G V b hV
    p.inclusion hv T s 1
  rw [mul_one] at hl
  rw [one_mul] at hr
  have hu : IsUnit (pointAlgebraHom G T 1 (affineRegularCoordinateMap G V b v)) := by
    rw [pointAlgebraHom_one, AlgHom.comp_apply]
    exact (isUnit_iff_ne_zero.mpr hv0).map
      (algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop)
  exact hu.mul_right_cancel (hr.symm.trans hl)

/-- A normalized coordinate in a covariant regular subspace forces occurrence
of its left character in the actual torus representation. -/
theorem affineRegularRepresentation_highest_ne_bot
    {lam : characterLattice p.torus}
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam))
    {f : algebra G} (hf : f ∈ V) (hf1 : counit (corepresentation G) f = 1) :
    p.representationWeightSpace (affineRegularRepresentation G V b hV) lam ≠ ⊥ := by
  intro hz
  let L : (Fin d → k) →ₗ[k] k :=
    (counit (corepresentation G)).toLinearMap.comp (affineRegularCoordinateMap G V b)
  have hle : (⨆ mu : characterLattice p.torus,
      p.representationWeightSpace (affineRegularRepresentation G V b hV) mu) ≤
        LinearMap.ker L := by
    apply iSup_le
    intro mu v hv
    change L v = 0
    by_cases hm : mu = lam
    · subst mu
      have hv0 : v = 0 := by rwa [hz, Submodule.mem_bot] at hv
      rw [hv0, map_zero]
    · by_contra hn
      exact hm (p.affineRegularRepresentation_weight_eq_of_counit_ne_zero V b hV hcov hv hn)
  rw [p.iSup_representationWeightSpace_eq_top] at hle
  let v : Fin d → k := b.equivFun ⟨f, hf⟩
  have hc : affineRegularCoordinateMap G V b v = f := by
    change ((b.equivFun.symm (b.equivFun ⟨f, hf⟩) : V) : algebra G) = f
    rw [LinearEquiv.symm_apply_apply]
  have hv := hle (show v ∈ (⊤ : Submodule k (Fin d → k)) from Submodule.mem_top)
  change L v = 0 at hv
  change counit (corepresentation G) (affineRegularCoordinateMap G V b v) = 0 at hv
  rw [hc, hf1] at hv
  exact one_ne_zero hv

/-- With a normalized coordinate, the left character occurs with multiplicity
exactly one in the covariant regular representation. -/
theorem affineRegularRepresentation_highest_finrank_eq_one
    {lam : characterLattice p.torus}
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam))
    {f : algebra G} (hf : f ∈ V) (hf1 : counit (corepresentation G) f = 1) :
    Module.finrank k (p.representationWeightSpace
      (affineRegularRepresentation G V b hV) lam) = 1 := by
  apply Nat.le_antisymm (p.affineRegularRepresentation_highest_finrank_le_one V b hV hcov)
  exact Submodule.one_le_finrank_iff.mpr
    (p.affineRegularRepresentation_highest_ne_bot V b hV hcov hf hf1)

/-- The actual regular socle of a realizing coordinate has a one-dimensional
highest character space, and every weight is below its realizing character. -/
theorem affineCovariantSocleRepresentation_weights
    {lam : characterLattice p.torus} {f : algebra G} (hf : p.IsRealizedBy lam f) :
    Module.finrank k (p.representationWeightSpace
      (affineCovariantSocleRepresentation G f) lam) = 1 ∧
    ∀ mu, p.representationWeightSpace (affineCovariantSocleRepresentation G f) mu ≠ ⊥ →
      lam - mu ∈ p.positiveRootMonoid := by
  let V := affineCovariantSocle G f
  let b := Module.finBasis k V
  have hcov : V ≤ leftCovariantSubspace p.negativeBorelHom
      (p.borelCharacterCoordinate lam) :=
    affineCovariantSocle_le_leftCovariantSubspace G _ _ hf.1
  constructor
  · exact p.affineRegularRepresentation_highest_finrank_eq_one V b
      (rightAct_mem_affineCovariantSocle G f) hcov (mem_affineCovariantSocle G f) hf.2.2
  · intro mu hmu
    exact p.affineRegularRepresentation_weight_le V b
      (rightAct_mem_affineCovariantSocle G f) hcov hmu

end Langlands.GroupScheme.SplitPinning
