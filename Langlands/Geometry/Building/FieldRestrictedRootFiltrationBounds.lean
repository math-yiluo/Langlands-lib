import Langlands.AlgebraicGeometry.PointTopology.HenselianSeparableValuedBounds
import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.GroupScheme.Torus.RationalCharacterSeparation
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-! # Algebraic boundedness under restriction of the ground field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [ValuativeRel k] [ValuativeRel K] [ValuativeExtension k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" i => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance fieldBoundsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

private instance fieldBoundsExtendedAffine : IsAffine (G_K).X.left := by
  have : IsAffineHom (G_K).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  exact isAffine_of_isAffineHom (G_K).X.hom

/-- Cofinality reflects boundedness of the preimage under actual rational scalar
extension, with the original valuative relation on the base. -/
theorem isAlgebraicallyBounded_preimage_rationalExtend
    (hcofinal : IsValuativelyCofinal k K)
    (B : Set (rationalPoints G_K)) (hB : IsAlgebraicallyBounded K (G_K).X B) :
    IsAlgebraicallyBounded k G.X ((rationalExtend k K G) ⁻¹' B) := by
  apply isAlgebraicallyBounded_of_geometricRationalPoint G.X hcofinal
  have he : geometricRationalPoint (K := K) G.X =
      (rationalExtend k K G : rationalPoints G → rationalPoints G_K) := by
    funext g
    rw [RationalCharacterSeparation.rationalExtend_eq_geometricRationalPointHom,
      geometricRationalPointHom_apply]
  rw [he]
  exact hB.mono (Set.image_preimage_subset _ _)

/-- A bounded upper root filtration bounds its exact ground-field preimage. -/
theorem isAlgebraicallyBounded_rootFiltration_fieldRestrict
    [Smooth G.X.hom] (i : S.toGrp ⟶ G)
    (hS : IsSplitTorus S.toGrp) (hcofinal : IsValuativelyCofinal k K)
    (ψ : RootFunctionFamily S_K G_K)
    (a : characterLattice S) (ha : a ≠ 0) (r : ℝ)
    (hB : IsAlgebraicallyBounded K (G_K).X
      (rootFiltration (S := S_K) (i_K i) ψ (a_K a) r)) :
    IsAlgebraicallyBounded k G.X
      (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a r) := by
  rw [rootFiltration_fieldRestrict i hS ψ a ha r]
  exact isAlgebraicallyBounded_preimage_rationalExtend hcofinal _ hB

/-- Ground-field restriction preserves bounds on an actual root filtration over
any compatible cofinal valuative extension, without altering its real depth. -/
def FieldRestrictedRootFiltrationBoundedStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [ValuativeRel k] [ValuativeRel K] [ValuativeExtension k K]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : S.toGrp ⟶ G) (_hS : IsSplitTorus S.toGrp)
    (_hcofinal : IsValuativelyCofinal k K)
    (ψ : RootFunctionFamily
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S) (baseChanged k K G))
    (a : characterLattice S) (_ha : a ≠ 0) (r : ℝ),
    IsAlgebraicallyBounded K (baseChanged k K G).X
      (rootFiltration ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ψ
        (characterLattice.baseChange (algebraBaseMap k K) S a) r) →
    IsAlgebraicallyBounded k G.X
      (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a r)

/-- Cofinal descent of regular-function bounds proves field restriction. -/
theorem fieldRestrictedRootFiltrationBounded :
    FieldRestrictedRootFiltrationBoundedStatement.{u} := by
  intro k K _ _ _ _ _ _ S G _ _ i hS hcofinal ψ a ha r hB
  exact isAlgebraicallyBounded_rootFiltration_fieldRestrict i hS hcofinal ψ a ha r hB

end Langlands.Geometry.Building
