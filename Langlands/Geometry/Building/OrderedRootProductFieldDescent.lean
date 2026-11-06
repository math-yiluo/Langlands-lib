import Langlands.GroupScheme.Rational.OrderedProductFpqcDescent
import Langlands.Geometry.Building.LocalRootProductInjectivity
import Langlands.Geometry.Building.RootFunctionFieldRestriction

/-! # Ordered actual root factors descend under field extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

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

/-- The set of actual rational points admitting an ordered factorization in
specified root filtrations. No subgroup closure is asserted. -/
def orderedRootFiltrationProduct
    (ψ : RootFunctionFamily S G) {n : ℕ} (a : Fin n → characterLattice S)
    (d : Fin n → ℝ) : Set (rationalPoints G) :=
  {g | ∃ x : ∀ r, rootFiltration i ψ (a r) (d r),
    (List.ofFn fun r => (x r : rationalPoints G)).prod = g}

/-- An actual ordered factorization of an extended original point descends
factor by factor. Opposite factor pairs are required only for the original
torus, and the supplied ordering is preserved. -/
theorem orderedRootFactors_fieldDescend
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    (g : rationalPoints G)
    (y : ∀ r, rootGroupPoints (S := S_K) i_K (a_K (a r)))
    (hy : (List.ofFn fun r => (y r : rationalPoints G_K)).prod =
      rationalExtend k K G g) :
    ∃ x : ∀ r, rootGroupPoints i (a r),
      (∀ r, rationalExtend k K G (x r) = (y r : rationalPoints G_K)) ∧
        (List.ofFn fun r => (x r : rationalPoints G)).prod = g := by
  classical
  have hroot (r : Fin n) : a r ∈ RelativeRoot.indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hrep (r : Fin n) :=
    RelativeRoot.subgroup_isClosedRepresentable hS i (a r) (hroot r).1.1.1
  choose H j hj hjc using hrep
  let q : (Over.map b).obj (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _) :=
    Over.homMk b (by simp)
  have hfpqc := fieldExtension_fpqc k K
  let : Flat b := hfpqc.2.1
  let : Surjective b := hfpqc.1
  let : QuasiCompact b := hfpqc.2.2
  let : EffectiveEpi q.left := by change EffectiveEpi b; infer_instance
  have hcomparison (z : rationalPoints G) :
      baseChangePointsEquiv b G (Over.mk (𝟙 _)) (rationalExtend k K G z) = q ≫ z := by
    apply Over.OverMorphism.ext
    exact rationalExtend_fst k K G z
  let y' : ∀ r, (RelativeRoot.subgroup i (a r)).carrier
      ((Over.map b).obj (Over.mk (𝟙 _))) :=
    fun r => RelativeRoot.subgroupPointsBaseChangeEquiv b i (a r) (Over.mk (𝟙 _)) (y r)
  have hy' : (List.ofFn fun r => (y' r : _ ⟶ G.X)).prod = q ≫ g := by
    change (List.ofFn fun r =>
      baseChangePointsEquiv b G (Over.mk (𝟙 _)) (y r)).prod = q ≫ g
    have h := congrArg (baseChangePointsEquiv b G (Over.mk (𝟙 _))) hy
    simpa only [map_list_prod, List.map_ofFn, Function.comp_def, hcomparison] using h
  obtain ⟨x, hxf, hx⟩ := RelativeRoot.orderedSubgroupFactors_descend j
    (fun r => RelativeRoot.subgroup i (a r)) hj
    (fun T => RelativeRoot.orderedRootSubgroupPoints_injective_of_hasOppositeFactorPairs
      i hS hE ν a hinj ha T) q g y' hy'
  refine ⟨x, ?_, hx⟩
  intro r
  apply (baseChangePointsEquiv b G (Over.mk (𝟙 _))).injective
  rw [hcomparison]
  exact hxf r

/-- Existence of an ordered product in arbitrary actual root filtrations
is preserved and reflected by field extension for the literal restricted
family. No root-datum valuation axiom is needed. -/
theorem exists_orderedRootFiltrationFactors_fieldExtend_iff
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    (ψ : RootFunctionFamily S_K G_K) (d : Fin n → ℝ) (g : rationalPoints G) :
    (∃ y : ∀ r, rootFiltration (S := S_K) i_K ψ (a_K (a r)) (d r),
      (List.ofFn fun r => (y r : rationalPoints G_K)).prod = rationalExtend k K G g) ↔
    (∃ x : ∀ r, rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ)
        (a r) (d r),
      (List.ofFn fun r => (x r : rationalPoints G)).prod = g) := by
  constructor
  · rintro ⟨y, hy⟩
    let y' : ∀ r, rootGroupPoints (S := S_K) i_K (a_K (a r)) :=
      fun r => ⟨(y r).val, (y r).property.1⟩
    obtain ⟨x, hxf, hx⟩ :=
      orderedRootFactors_fieldDescend i hS hE ν a hinj ha g y' hy
    let x' : ∀ r, rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ)
        (a r) (d r) := fun r => ⟨(x r).val, (x r).property, by
      change (d r : WithTop ℝ) ≤ ψ (a_K (a r)) (rationalExtend k K G (x r))
      rw [hxf r]
      exact (y r).property.2⟩
    exact ⟨x', hx⟩
  · rintro ⟨x, hx⟩
    let y : ∀ r, rootFiltration (S := S_K) i_K ψ (a_K (a r)) (d r) :=
      fun r => ⟨rationalExtend k K G (x r),
        rationalExtend_mem_rootGroupPoints i (a r) (x r).property.1,
        (x r).property.2⟩
    refine ⟨y, ?_⟩
    simpa only [map_list_prod, List.map_ofFn, Function.comp_def] using
      congrArg (rationalExtend k K G) hx

/-- Actual field extension preserves and reflects membership in the ordered
root-filtration product set for the literal restricted family. -/
theorem mem_orderedRootFiltrationProduct_fieldExtend_iff
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    (ψ : RootFunctionFamily S_K G_K) (d : Fin n → ℝ) (g : rationalPoints G) :
    rationalExtend k K G g ∈ orderedRootFiltrationProduct (i_K) ψ
        (fun r => a_K (a r)) d ↔
      g ∈ orderedRootFiltrationProduct i (RootFunctionFamily.fieldRestrict (k := k) ψ)
        a d :=
  exists_orderedRootFiltrationFactors_fieldExtend_iff i hS hE ν a hinj ha ψ d g

end Langlands.Geometry.Building
