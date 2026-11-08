import Langlands.Geometry.Building.RootValueTorusFieldRestriction
import Langlands.Geometry.Building.RootValueTorusDouble
import Langlands.Geometry.Building.RootFunctionFieldShifts
import Langlands.Geometry.Building.RootFunctionNontriviality

/-! # Scalar axioms for actual torus restriction followed by field restriction -/

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

omit [Smooth G.X.hom] in
private theorem rationalExtend_injective :
    Function.Injective (rationalExtend k K G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro x y h
  apply (rationalCoeffEquiv k G).injective
  apply GaloisPoint.extend_injective k K G
  simpa only [baseChangeCoeffEquiv_rationalExtend] using
    congrArg (baseChangeCoeffEquiv k K G) h

variable {T : CommGroupScheme (Spec (CommRingCat.of K))}

omit [Mono i.hom.hom.left] in
/-- Both support normalization laws hold for the literal torus-then-field family. -/
theorem torusFieldRestrictedRootFunctionFamily_normalization
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K) :
    (∀ a, a ∉ relativeRoots i → ∀ g,
      torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a g = ⊤) ∧
    (∀ a ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i a →
      torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a g = ⊤) := by
  apply RootFunctionFamily.fieldRestrict_normalization hS
    (torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f)
  · intro a ha g
    apply torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots
    simpa only [hfactor] using ha
  · intro a _ g hg
    apply torusRestrictedRootFunctionFamily_eq_top_of_not_mem
    simpa only [hfactor] using hg

omit [Mono i.hom.hom.left] in
/-- The exact identity criterion survives actual field extension and torus restriction. -/
theorem torusFieldRestrictedRootFunctionFamily_eq_top_iff
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a) :
    torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a g = ⊤ ↔
      g = 1 := by
  have haK : (a_K a) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  have hgK : rationalExtend k K G g ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (a_K a) := by
    rw [hfactor]
    exact rationalExtend_mem_rootGroupPoints (K := K) i a hg
  unfold torusFieldRestrictedRootFunctionFamily
  rw [RootFunctionFamily.fieldRestrict_apply,
    torusRestrictedRootFunctionFamily_eq_top_iff (hS.baseChange b) hT hE hφ f
      (a_K a) haK (rationalExtend k K G g) hgK]
  constructor
  · intro h
    apply rationalExtend_injective (K := K) (G := G)
    simpa only [map_one] using h
  · rintro rfl
    exact map_one _

omit [Mono i.hom.hom.left] in
/-- V1 identity closure is inherited from the exact subgroup preimage. -/
theorem torusFieldRestrictedRootFunctionFamily_one_mem
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ) :
    (1 : rationalPoints G) ∈ rootFiltration i
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r := by
  rw [rootFiltration_torusFieldRestrictedRootFunctionFamily i hS hT hE hφ f hfactor a ha r]
  exact Subgroup.one_mem _

omit [Mono i.hom.hom.left] in
/-- V1 multiplication closure is inherited from the exact subgroup preimage. -/
theorem torusFieldRestrictedRootFunctionFamily_mul_mem
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ)
    (g h : rationalPoints G)
    (hg : g ∈ rootFiltration i
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r)
    (hh : h ∈ rootFiltration i
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r) :
    g * h ∈ rootFiltration i
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r := by
  rw [rootFiltration_torusFieldRestrictedRootFunctionFamily i hS hT hE hφ f hfactor a ha r]
    at hg hh ⊢
  exact Subgroup.mul_mem _ hg hh

omit [Mono i.hom.hom.left] in
/-- V1 inversion closure is inherited from the exact subgroup preimage. -/
theorem torusFieldRestrictedRootFunctionFamily_inv_mem
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ)
    (g : rationalPoints G)
    (hg : g ∈ rootFiltration i
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r) :
    g⁻¹ ∈ rootFiltration i
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) a r := by
  rw [rootFiltration_torusFieldRestrictedRootFunctionFamily i hS hT hE hφ f hfactor a ha r]
    at hg ⊢
  exact Subgroup.inv_mem _ hg

omit [Mono i.hom.hom.left] in
/-- Full V4 holds on each actual original doubled-root group. -/
theorem torusFieldRestrictedRootFunctionFamily_double
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i)
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints i (2 • a)) :
    torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f (2 • a) g =
      2 • torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a g := by
  have haK : (a_K a) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  have h2aK : 2 • (a_K a) ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [hfactor]
    simpa only [map_nsmul, relativeRoots] using
      (mem_roots_baseChange_iff (K := K) G S hS i (2 • a)).mpr h2a
  have hgK : rationalExtend k K G g ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • (a_K a)) := by
    rw [hfactor]
    simpa only [map_nsmul] using
      rationalExtend_mem_rootGroupPoints (K := K) i (2 • a) hg
  simpa only [torusFieldRestrictedRootFunctionFamily,
    RootFunctionFamily.fieldRestrict_apply, map_nsmul] using
    torusRestrictedRootFunctionFamily_double (hS.baseChange b) hT hE hφ f
      (a_K a) haK h2aK (rationalExtend k K G g) hgK

omit [Mono i.hom.hom.left] in
/-- Integral powers of an original torus point give an injective sequence
in the original root-value image of the torus-then-field family. -/
def torusFieldRestrictedRootValueEmbedding
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible j (fun t => (ω t).toAdd) φ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    ℤ ↪ (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a ''
      (rootGroupPoints i a : Set (rationalPoints G))) := by
  let ωk := ω.comp (Units.map (algebraMap k K).toMonoidHom)
  have hc : IsSplitTorusCompatible i (fun t => (ωk t).toAdd)
      (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f) :=
    torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible i hS hT hE hφ f
      hfactor ω hcompat
  exact hc.rootValueEmbedding ωk hS hω
    (torusFieldRestrictedRootFunctionFamily_eq_top_iff i hS hT hE hφ f hfactor) ha

omit [Mono i.hom.hom.left] in
/-- V0 follows from actual torus covariance and a unit character nontrivial
on original field units, without a full lower-torus valuation upstairs. -/
theorem torusFieldRestrictedRootFunctionFamily_image_infinite
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible j (fun t => (ω t).toAdd) φ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a ''
      (rootGroupPoints i a : Set (rationalPoints G))).Infinite := by
  let e := torusFieldRestrictedRootValueEmbedding i hS hT hE hφ f hfactor ω hcompat hω ha
  exact Set.infinite_of_injective_forall_mem
    (Subtype.val_injective.comp e.injective) (fun n => (e n).property)

omit [Mono i.hom.hom.left] in
/-- In particular the actual original root-value image has at least three elements. -/
theorem torusFieldRestrictedRootFunctionFamily_three_le_encard
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible j (fun t => (ω t).toAdd) φ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    3 ≤ (torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a ''
      (rootGroupPoints i a : Set (rationalPoints G))).encard := by
  rw [(torusFieldRestrictedRootFunctionFamily_image_infinite i hS hT hE hφ f hfactor
    ω hcompat hω ha).encard_eq]
  exact le_top

end Langlands.Geometry.Building
