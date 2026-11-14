import Langlands.Geometry.Building.RestrictedRootFiltrationBounds
import Langlands.Geometry.Building.FieldRestrictedRootFiltrationBounds
import Langlands.Geometry.Building.RootValueTorusFieldRestriction

/-! # Algebraic bounds under torus restriction followed by field restriction -/

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
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of K))}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" i => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance torusFieldBoundsExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance torusFieldBoundsExtendedSmooth : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance torusFieldBoundsExtendedFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Bounds at all depths for the upper family descend through the exact
canonical torus-then-field restriction on every actual original root. -/
theorem isAlgebraicallyBounded_rootFiltration_torusFieldRestrict
    (i : S.toGrp ⟶ G) {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (hcofinal : IsValuativelyCofinal k K)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K i)
    (hB : ∀ a ∈ relativeRoots j, ∀ r : ℝ,
      IsAlgebraicallyBounded K (G_K).X (rootFiltration j φ a r))
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ) :
    IsAlgebraicallyBounded k G.X
      (rootFiltration i (torusFieldRestrictedRootFunctionFamily (G := G) (j := j)
        hS hT hE hφ f) a r) := by
  have haK : (a_K a) ∈ relativeRoots (T := S_K) (i_K i) :=
    (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  rw [rootFiltration_torusFieldRestrictedRootFunctionFamily i hS hT hE hφ f hfactor a ha r]
  change IsAlgebraicallyBounded k G.X ((rationalExtend k K G) ⁻¹'
    (torusRestrictedRootDepthSubgroup hφ f (a_K a) r : Set (rationalPoints G_K)))
  apply isAlgebraicallyBounded_preimage_rationalExtend hcofinal
  apply isAlgebraicallyBounded_torusRestrictedRootDepthSubgroup
    (hS.baseChange b) hT hE hφ f (a_K a) haK.1 r
  intro c hc m _
  exact hB c hc _

/-- All-depth boundedness transport through canonical torus-then-field restriction. -/
def TorusFieldRestrictedRootFiltrationBoundedStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [ValuativeRel k] [ValuativeRel K] [ValuativeExtension k K]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of K)))
    (i : S.toGrp ⟶ G) (j : T.toGrp ⟶ baseChanged k K G) [Mono j.hom.hom.left]
    (φ : RootFunctionFamily T (baseChanged k K G))
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ),
    IsValuativelyCofinal k K →
    ∀ (f : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S ⟶ T),
      CommGroupScheme.groupHom f ≫ j = (GroupScheme.baseChange (algebraBaseMap k K)).map i →
      (∀ a ∈ relativeRoots j, ∀ r : ℝ,
        IsAlgebraicallyBounded K (baseChanged k K G).X (rootFiltration j φ a r)) →
      ∀ a ∈ relativeRoots i, ∀ r : ℝ,
        IsAlgebraicallyBounded k G.X
          (rootFiltration i (torusFieldRestrictedRootFunctionFamily (G := G) (j := j)
            hS hT hE hφ f) a r)

/-- Exact subgroup preimages and finite bounded products prove the transport statement. -/
theorem torusFieldRestrictedRootFiltrationBounded :
    TorusFieldRestrictedRootFiltrationBoundedStatement.{u} := by
  intro k K _ _ _ _ _ _ S G _ _ _ T i j _ φ hS hT hE hφ hcofinal f hfactor hB a ha r
  exact isAlgebraicallyBounded_rootFiltration_torusFieldRestrict i hS hT hE hφ hcofinal
    f hfactor hB a ha r

end Langlands.Geometry.Building
