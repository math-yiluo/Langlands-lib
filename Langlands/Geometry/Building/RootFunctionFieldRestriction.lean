import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.Geometry.Building.SplitTorusTranslationBaseChange

/-! # Actual root-group and root-function restriction under field extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private theorem pointComparison_rationalExtend (g : rationalPoints G) :
    baseChangePointsEquiv b G (Over.mk (𝟙 _)) (rationalExtend k K G g) =
      G.constantPoint g ((Over.map b).obj (Over.mk (𝟙 _))) := by
  rw [rationalExtend_eq_baseChangeBasePoint]
  simpa only [constantPoint_self] using
    baseChangePointsEquiv_constantPoint b G g (Over.mk (𝟙 _))

/-- Actual rational scalar extension preserves the original root group. -/
theorem rationalExtend_mem_rootGroupPoints (a : characterLattice S)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    rationalExtend k K G g ∈ rootGroupPoints (S := S_K) i_K (a_K a) := by
  change rationalExtend k K G g ∈ (RelativeRoot.subgroup (S := S_K) i_K (a_K a)).carrier _
  rw [RelativeRoot.subgroup_baseChange, SubgroupFunctor.mem_baseChange,
    pointComparison_rationalExtend]
  let q : (Over.map b).obj (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _) :=
    Over.homMk b (by simp)
  change q ≫ g ∈ (RelativeRoot.subgroup i a).carrier _
  exact (RelativeRoot.subgroup i a).comp_mem q hg

/-- The actual field-extension map restricted to existing root-group points. -/
def rootGroupPointsFieldExtend (a : characterLattice S) :
    rootGroupPoints i a →* rootGroupPoints (S := S_K) i_K (a_K a) where
  toFun g := ⟨rationalExtend k K G g.val,
    rationalExtend_mem_rootGroupPoints (K := K) i a g.property⟩
  map_one' := Subtype.ext (map_one (rationalExtend k K G))
  map_mul' g h := Subtype.ext (map_mul (rationalExtend k K G) g.val h.val)

section Reflection

variable (hS : IsSplitTorus S.toGrp) [IsAffineHom G.X.hom] [Smooth G.X.hom]

include hS in
/-- For a nonzero character, membership in the actual root group is also reflected.
The represented subgroup is constructed from splitness and smoothness. -/
theorem rationalExtend_mem_rootGroupPoints_iff (a : characterLattice S) (ha : a ≠ 0)
    (g : rationalPoints G) :
    rationalExtend k K G g ∈ rootGroupPoints (S := S_K) i_K (a_K a) ↔
      g ∈ rootGroupPoints i a := by
  constructor
  · intro hg
    change rationalExtend k K G g ∈ (RelativeRoot.subgroup (S := S_K) i_K (a_K a)).carrier _ at hg
    rw [RelativeRoot.subgroup_baseChange, SubgroupFunctor.mem_baseChange,
      pointComparison_rationalExtend] at hg
    obtain ⟨U, j, hj, _⟩ := RelativeRoot.subgroup_isClosedRepresentable hS i a ha
    let : Mono j.hom.hom := hj.1
    let q : (Over.map b).obj (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _) :=
      Over.homMk b (by simp)
    have hfpqc := fieldExtension_fpqc k K
    let : Flat b := hfpqc.2.1
    let : Surjective b := hfpqc.1
    let : QuasiCompact b := hfpqc.2.2
    let : EffectiveEpi q.left := by change EffectiveEpi b; infer_instance
    change g ∈ (RelativeRoot.subgroup i a).carrier _
    rw [← hj.2] at hg ⊢
    exact SubgroupFunctor.mem_range_of_comp_mem_range j q hg
  · exact rationalExtend_mem_rootGroupPoints i a

end Reflection

namespace RootFunctionFamily

variable {i}

/-- Restrict the actual upstairs family along character pullback and rational scalar extension. -/
def fieldRestrict (ψ : RootFunctionFamily S_K G_K) : RootFunctionFamily S G :=
  ⟨fun a g => ψ (a_K a) (rationalExtend k K G g)⟩

@[simp] theorem fieldRestrict_apply (ψ : RootFunctionFamily S_K G_K)
    (a : characterLattice S) (g : rationalPoints G) :
    fieldRestrict (k := k) ψ a g = ψ (a_K a) (rationalExtend k K G g) := rfl

/-- Restriction intertwines actual real cocharacter translation, with no compatibility premise. -/
theorem fieldRestrict_vadd (hS : IsSplitTorus S.toGrp)
    (ψ : RootFunctionFamily S_K G_K) (v : V S) :
    fieldRestrict (k := k) (splitCocharacterBaseChange (K := K) S hS v +ᵥ ψ) =
      v +ᵥ fieldRestrict (k := k) ψ := by
  ext a g
  simp only [fieldRestrict_apply, vadd_apply, eval_splitCocharacterBaseChange]

end RootFunctionFamily

/-- The nonzero-root filtration downstairs is exactly the preimage of the actual
upstairs filtration of the restricted family. -/
theorem rootFiltration_fieldRestrict (hS : IsSplitTorus S.toGrp)
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (ψ : RootFunctionFamily S_K G_K)
    (a : characterLattice S) (ha : a ≠ 0) (r : ℝ) :
    rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a r =
      (rationalExtend k K G) ⁻¹' rootFiltration (S := S_K) i_K ψ (a_K a) r := by
  ext g
  simp only [mem_rootFiltration, RootFunctionFamily.fieldRestrict_apply, Set.mem_preimage,
    rationalExtend_mem_rootGroupPoints_iff i hS a ha]

end Langlands.Geometry.Building
