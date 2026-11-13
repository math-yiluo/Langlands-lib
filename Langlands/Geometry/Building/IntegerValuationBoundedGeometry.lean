import Langlands.Geometry.Building.UnramifiedVertexFixerStatements
import Langlands.GroupScheme.Rational.CharacterPolynomialGrowth
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Bounded-subgroup geometry for integer-valued buildings -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.IntegerValuation

variable {k : Type u} [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Algebraic boundedness of a subgroup forces all actual rational characters
into the unit-value subgroup of an integer-valued valuation. -/
theorem subgroup_le_characterValuationKernel_of_isAlgebraicallyBounded
    (B : Subgroup (rationalPoints G))
    (hB : IsAlgebraicallyBounded k G.X (B : Set (rationalPoints G))) :
    B ≤ characterValuationKernel v G := by
  intro g hg
  rw [mem_characterValuationKernel]
  intro χ
  obtain ⟨b, hb, hbound⟩ := hB (rationalCharacterSection χ)
  have hupper (a : rationalPoints G) (ha : a ∈ B) :
      WithZero.log (v (rationalCharacterEval χ a : k)) ≤ 0 := by
    by_contra! hpos
    obtain ⟨n, hn⟩ := exists_lt_nsmul hpos (WithZero.log (v b))
    have hv := (v.vle_iff_le).1 (hbound (a ^ n) (B.pow_mem ha n))
    rw [rationalPointAlgebraHom_rationalCharacterSection, map_pow,
      Units.val_pow_eq_pow_val, map_pow] at hv
    have hl := (WithZero.log_le_log
      (pow_ne_zero n (v.ne_zero_of_unit _)) (v.ne_zero_iff.mpr hb)).2 hv
    rw [WithZero.log_pow] at hl
    exact (not_le_of_gt hn) hl
  have hinv := hupper g⁻¹ (B.inv_mem hg)
  simp only [map_inv, Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv] at hinv
  have hzero : WithZero.log (v (rationalCharacterEval χ g : k)) = 0 :=
    le_antisymm (hupper g hg) (neg_nonpos.mp hinv)
  have he := WithZero.exp_log (v.ne_zero_of_unit (rationalCharacterEval χ g))
  rw [hzero, WithZero.exp_zero] at he
  exact he.symm

end Langlands.Geometry.Building.IntegerValuation

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k] [ValuativeRel k]
    {v : Valuation k (WithZero (Multiplicative ℤ))} [v.Compatible]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (C : IntegerValuationBuildingData v G)

private instance boundedGeometryAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Three geometric inputs for maximal boundedness of vertex one-stabilizers.
This predicate supplies no construction of any of its fields. -/
structure HasAlgebraicallyBoundedGeometry : Prop where
  /-- Each actual one-stabilizer is algebraically bounded. -/
  bounded_oneStabilizer : ∀ y : C.ReducedBuilding,
    IsAlgebraicallyBounded k G.X (C.oneStabilizer y : Set (rationalPoints G))
  /-- Every algebraically bounded subgroup fixes a point of the original quotient. -/
  exists_fixed : ∀ B : Subgroup (rationalPoints G),
    IsAlgebraicallyBounded k G.X (B : Set (rationalPoints G)) →
      ∃ y : C.ReducedBuilding, ∀ g ∈ B, g • y = y
  /-- The fixed locus of a vertex one-stabilizer is its vertex alone. -/
  vertex_fixed : ∀ y : C.ReducedBuilding, C.IsVertex y →
    ∀ z : C.ReducedBuilding, (∀ g ∈ C.oneStabilizer y, g • z = z) → z = y

/-- The geometric inputs imply maximal algebraic boundedness at each vertex. -/
theorem maximal_oneStabilizer_of_hasAlgebraicallyBoundedGeometry
    (hC : C.HasAlgebraicallyBoundedGeometry) (y : C.ReducedBuilding)
    (hy : C.IsVertex y) :
    Maximal (fun B : Subgroup (rationalPoints G) =>
      IsAlgebraicallyBounded k G.X (B : Set (rationalPoints G)))
      (C.oneStabilizer y) := by
  refine ⟨hC.bounded_oneStabilizer y, ?_⟩
  intro B hB hle
  obtain ⟨z, hz⟩ := hC.exists_fixed B hB
  have hzy : z = y := hC.vertex_fixed y hy z (fun g hg => hz g (hle hg))
  subst z
  have hkernel := IntegerValuation.subgroup_le_characterValuationKernel_of_isAlgebraicallyBounded
    v G B hB
  intro g hg
  exact C.mem_oneStabilizer.mpr ⟨hkernel hg, hz g hg⟩

end Langlands.Geometry.Building.IntegerValuationBuildingData

namespace Langlands.Geometry.Building.MaximalUnramified

open Langlands.LocalGalois.Separable

/-- The three geometric inputs on the actual unramified field, using the
prescribed valuative relation. This is an unproved input proposition. -/
def BoundedGeometryStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : BuildingData F G),
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    C.HasAlgebraicallyBoundedGeometry

/-- The new integer valuation is compatible with the required valuative
relation on the same inertia fixed field. -/
theorem valuation_compatible
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    (valuation F).Compatible := by
  letI := ValuativeRel.ofValuation (fixedFieldValued F).v
  letI : (fixedFieldValued F).v.Compatible := Valuation.Compatible.ofValuation _
  exact ⟨fun a b => ((fixedFieldValued F).v.vle_iff_le).trans
    ((valuation_isEquiv F) a b).symm⟩

/-- The three geometric inputs, once proved, give the unchanged exact target.
The character-kernel step is proved over the integer-valued field directly. -/
theorem vertexOneStabilizerMaximalBounded_of_boundedGeometry
    (h : BoundedGeometryStatement.{u}) :
    VertexOneStabilizerMaximalBoundedStatement.{u} := by
  intro F _ _ _ _ G _ C y hy
  letI := ValuativeRel.ofValuation (fixedFieldValued F).v
  letI : (valuation F).Compatible := valuation_compatible F
  exact C.maximal_oneStabilizer_of_hasAlgebraicallyBoundedGeometry (h F G C) y hy

end Langlands.Geometry.Building.MaximalUnramified
