import Langlands.Geometry.Building.RootDepthCommutatorFieldDescent
import Langlands.Geometry.Building.RootDepthTorusCollectionData
import Langlands.Geometry.Building.RootValueTorusCovariance

/-! # Actual torus restriction followed by field restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {T : CommGroupScheme (Spec (CommRingCat.of K))}

omit [Mono i.hom.hom.left] in
/-- Restrict the canonical upper-torus scalar family on actual extended points. -/
def torusFieldRestrictedRootFunctionFamily
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) : RootFunctionFamily S G :=
  RootFunctionFamily.fieldRestrict (k := k) (K := K) (S := S) (G := G)
    (torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f)

omit [Mono i.hom.hom.left] in
/-- The exact preimage of the canonical upper-generated depth subgroup. -/
def torusFieldRestrictedRootDepthSubgroup
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hφ : IsRootDatumValuation j φ) (f : S_K ⟶ T)
    (a : characterLattice S) (r : ℝ) : Subgroup (rationalPoints G) :=
  (torusRestrictedRootDepthSubgroup (i := j) hφ f (a_K a) r).comap (rationalExtend k K G)

omit [Mono i.hom.hom.left] in
/-- Actual factorization through the enlarged upper torus supplies weak data
on the original torus pullback without a full valuation there. -/
def torusRestrictedRootDepthCollectionData_of_fieldFactorization
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K) :
    RootDepthCollectionData (k := K) (S := S_K) (G := G_K) i_K
      (torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f) := by
  simpa only [hfactor] using
    torusRestrictedRootDepthCollectionData (i := j) (hS.baseChange b) hT hE hφ f

omit [Mono i.hom.hom.left] in
/-- Every original finite root level is exactly the actual canonical subgroup
preimage, with no change in its real depth. -/
theorem rootFiltration_torusFieldRestrictedRootFunctionFamily
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ) :
    rootFiltration i (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r =
      (torusFieldRestrictedRootDepthSubgroup (G := G) (j := j) hφ f a r : Set (rationalPoints G)) := by
  have haK : (a_K a) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  unfold torusFieldRestrictedRootFunctionFamily
  rw [rootFiltration_fieldRestrict i hS _ a ha.1 r, ← hfactor,
    rootFiltration_torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f
      (a_K a) haK r]
  rfl

/-- The actual torus-then-field family satisfies full V3 on original roots.
No root-datum valuation for the lower torus over K is assumed. -/
theorem torusFieldRestrictedRootFunctionFamily_commutator
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (a' : characterLattice S) (ha' : a' ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a' : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) (r s : ℝ) :
    ⁅Subgroup.closure (rootFiltration i
        (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r),
      Subgroup.closure (rootFiltration i
        (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a' s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • a' ∈ relativeRoots i),
        rootFiltration i (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f)
          (p • a + q • a') (p * r + q * s)) := by
  exact (torusRestrictedRootDepthCollectionData_of_fieldFactorization i hS hT hE hφ f
    hfactor).fieldRestrict_commutator i hS hEbase a ha a' ha' hnon r s

omit [Mono i.hom.hom.left] in
/-- Split-torus covariance descends with the same upper unit character restricted
to original field units. -/
theorem torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible j (fun t => (ω t).toAdd) φ) :
    IsSplitTorusCompatible i
      (fun t => (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd)
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) := by
  have hc := torusRestrictedRootFunctionFamily_isSplitTorusCompatible
    ω (hS.baseChange b) hT hE hφ hcompat f
  rw [hfactor] at hc
  exact RootFunctionFamily.fieldRestrict_isSplitTorusCompatible hS hc

end Langlands.Geometry.Building
