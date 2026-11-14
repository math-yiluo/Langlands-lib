import Langlands.Geometry.Building.Kottwitz.TorusGaloisDescent
import Langlands.Geometry.Building.Kottwitz.TorusGaloisSplitting

/-! # Equivariance and rational descent of the torus Kottwitz map -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T.toGrp)

/-- Equivariance places the restriction to rational points in the invariant target. -/
def torusKottwitzRestrictionOfEquivariant (h : TorusKottwitzEquivariant F T hT) :
    rationalPoints T.toGrp →* Multiplicative (TorusInvariantTarget F T) where
  toFun t := Multiplicative.ofAdd
    ⟨(torusKottwitz F F T hT (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp
      (rationalCoeffEquiv F T.toGrp t))).toAdd, fun σ => by
        have heq := h σ (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp
          (rationalCoeffEquiv F T.toGrp t))
        rw [GaloisPoint.conjugate_extend] at heq
        exact heq.symm⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp

/-- The explicit invariant restriction satisfies the original restriction predicate. -/
theorem torusKottwitzRestrictionOfEquivariant_spec (h : TorusKottwitzEquivariant F T hT) :
    IsTorusKottwitzRestriction F T hT (torusKottwitzRestrictionOfEquivariant F T hT h) :=
  fun _ => rfl

/-- Inclusion into the inertia quotient makes the invariant restriction unique. -/
theorem torusKottwitzRestriction_unique
    {κ κ' : rationalPoints T.toGrp →* Multiplicative (TorusInvariantTarget F T)}
    (hκ : IsTorusKottwitzRestriction F T hT κ)
    (hκ' : IsTorusKottwitzRestriction F T hT κ') : κ = κ' := by
  ext t
  exact congrArg Multiplicative.toAdd ((hκ t).trans (hκ' t).symm)

/-- Unique existence and the selected-map law follow from equivariance. -/
theorem torusKottwitzRestriction_existsUnique_of_equivariant
    (h : TorusKottwitzEquivariant F T hT) :
    (∃! κ, IsTorusKottwitzRestriction F T hT κ) ∧
      IsTorusKottwitzRestriction F T hT (torusKottwitzRational F T hT) := by
  have hex : ∃ κ, IsTorusKottwitzRestriction F T hT κ :=
    ⟨_, torusKottwitzRestrictionOfEquivariant_spec F T hT h⟩
  exact ⟨⟨_, hex.choose_spec, fun κ hκ =>
    torusKottwitzRestriction_unique F T hT hκ hex.choose_spec⟩,
    Classical.epsilon_spec hex⟩

/-- KP Proposition 11.1.1: equivariance and the unique invariant-valued rational restriction. -/
theorem torusKottwitzDescent : TorusKottwitzDescentStatement.{u} := by
  intro F _ _ _ _ T hT
  let : IsAffine T.X.left := torusIsAffine F T hT
  obtain ⟨L, _, _, _, hL⟩ := exists_normal_splitting F T hT
  have heq := torusKottwitzEquivariant_of_normal_splitting F T hT L hL
  exact ⟨heq, torusKottwitzRestriction_existsUnique_of_equivariant F T hT heq⟩

end Langlands.Geometry.Building.Kottwitz
