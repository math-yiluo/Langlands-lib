import Langlands.Geometry.Building.RootPointLieFieldExtension
import Langlands.Geometry.Building.RootFieldCoordinatesOfTorus
import Langlands.GroupScheme.Rational.RootPointLieTorusRestriction

/-! # Actual split-root products of root-field points -/

noncomputable section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Absence of higher restricted roots excludes higher roots above each
character with that nonzero restriction. -/
theorem HasNoHigherRoots.of_restriction
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    {β : characterLattice T} (hβ : f ≫ β = a) : HasNoHigherRoots j β := by
  intro n hn hroot
  apply hhigh n hn
  exact (mem_roots_comp_iff hT hS f j (n • a)).mpr
    ⟨hS.nsmul_ne_zero ha (by omega), n • β, hroot, by
      rw [Preadditive.comp_nsmul, hβ]⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- Equality of the acting homomorphism and of the ambient point preserves
the intrinsic point-to-Lie vector. -/
theorem rootPointLieEquiv_congr
    [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp) {i i' : S.toGrp ⟶ G} (hi : i = i')
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : HasNoHigherRoots i a) (hhigh' : HasNoHigherRoots i' a)
    (x : (subgroup i a).carrier (Over.mk (𝟙 _)))
    (y : (subgroup i' a).carrier (Over.mk (𝟙 _)))
    (hxy : x.val = y.val) :
    (rootPointLieEquiv hS i ha hhigh (Additive.ofMul x) : Additive (lieKernel G k)) =
      (rootPointLieEquiv hS i' ha hhigh' (Additive.ofMul y) : Additive (lieKernel G k)) := by
  subst i'
  have h : x = y := Subtype.ext hxy
  subst y
  rfl

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "f_L" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f
local notation "i" => CommGroupScheme.groupHom f ≫ j
local notation "i_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_L" a => characterLattice.baseChange b S a

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local instance : LocallyOfFiniteType (G_L).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local instance : Smooth (G_L).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

variable (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)

/-- The actual rational root point associated with an element of the root field. -/
def rootOrbitFieldPoint (x : rootOrbitField k L j β) : rootGroupPoints (k := k) (S := S) (G := G) i a :=
  ((RelativeRoot.rootPointLieEquiv (k := k) (S := S) (G := G) (a := a) hS i ha hhigh).symm
    (rootOrbitFieldWeightSpaceEquiv (S := S) (T := T) (G := G) k L j f a hG hj hS hT ha β horbit x)).toMul

/-- Scalar extension of the actual root-field point has the literal ambient
Lie vector reconstructed from its invariant orbit tuple. -/
theorem rootOrbitFieldPoint_extendedLie (x : rootOrbitField k L j β) :
    (RelativeRoot.rootPointLieEquiv (k := L) (S := S_L) (G := G_L)
        (a := a_L a) (hS.baseChange b) i_L
        ((characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha)
        (RelativeRoot.HasNoHigherRoots.baseChange (k := k) (K := L)
          (S := S) (G := G) (a := a) hS i hhigh)
        (Additive.ofMul (rootGroupPointsFieldExtend (k := k) (K := L)
          (S := S) (G := G) i a
          (rootOrbitFieldPoint k L f j hG hj hS hT ha hhigh β horbit x))) :
      Additive (lieKernel G_L L)) =
      (rootOrbitFieldFixedSpanEquiv k L j hG hj hT β x).val.val := by
  rw [rootPointLieEquiv_fieldExtend]
  change (rootWeightSpaceFieldExtend (K := L) i a
      ((RelativeRoot.rootPointLieEquiv (k := k) (S := S) (G := G) (a := a) hS i ha hhigh)
        (Additive.ofMul ((RelativeRoot.rootPointLieEquiv (k := k) (S := S) (G := G) (a := a) hS i ha hhigh).symm
          (rootOrbitFieldWeightSpaceEquiv (S := S) (T := T) (G := G) k L j f a hG hj hS hT ha β horbit x)).toMul)) :
        Additive (lieKernel G_L L)) = _
  rw [ofMul_toMul, AddEquiv.apply_symm_apply, rootWeightSpaceFieldExtend_val,
    Lie.schemeScalarExtension_tmul, one_smul]
  exact rootOrbitFieldWeightSpaceEquiv_baseChange k L j f a hG hj hS hT ha β horbit x

omit [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
include horbit in
/-- Every root in the orbit has the given restriction. -/
theorem rootOrbit_restriction (r : MulAction.orbit (L ≃ₐ[k] L) β) :
    f_L ≫ r.val.val = a_L a := by
  have hr : r.val ∈ rootRestrictionFiber k L j f a := horbit ▸ r.property
  exact hr

omit [FiniteDimensional k L] [IsGalois k L] in
include hS hT ha hhigh horbit in
/-- The original no-higher-root condition excludes higher roots at each
actual upper orbit root. -/
theorem rootOrbit_hasNoHigherRoots (r : MulAction.orbit (L ≃ₐ[k] L) β) :
    RelativeRoot.HasNoHigherRoots (T := T_L) (G := G_L) j_L r.val.val := by
  apply RelativeRoot.HasNoHigherRoots.of_restriction (hS.baseChange b) hT f_L j_L
    ((characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha)
    (by
      have hh := RelativeRoot.HasNoHigherRoots.baseChange (k := k) (K := L)
        (S := S) (G := G) (a := a) hS i hhigh
      rw [Functor.map_comp] at hh
      exact hh)
  exact rootOrbit_restriction k L f j β horbit r

/-- The actual split root-point coordinate induced by the coherent orbit Lie
line coordinate. -/
def rootOrbitPointEquiv (r : MulAction.orbit (L ≃ₐ[k] L) β) :
    Multiplicative L ≃* rootGroupPoints (k := L) (S := T_L) (G := G_L) j_L r.val.val :=
  AddEquiv.toMultiplicativeLeft
    ((rootOrbitLineEquiv k L j hG hj hT β r).toAddEquiv.trans
      (RelativeRoot.rootPointLieEquiv (k := L) (S := T_L) (G := G_L)
        (a := r.val.val) hT j_L r.val.property.1
        (rootOrbit_hasNoHigherRoots k L f j hS hT ha hhigh β horbit r)).symm)

omit [IsGalois k L] in
/-- The actual split root-point coordinate has the chosen coherent Lie-line
coordinate. -/
theorem rootOrbitPointEquiv_lie
    (r : MulAction.orbit (L ≃ₐ[k] L) β) (z : L) :
    RelativeRoot.rootPointLieEquiv (k := L) (S := T_L) (G := G_L)
        (a := r.val.val) hT j_L r.val.property.1
        (rootOrbit_hasNoHigherRoots k L f j hS hT ha hhigh β horbit r)
        (Additive.ofMul (rootOrbitPointEquiv k L f j hG hj hS hT ha hhigh β horbit r
          (Multiplicative.ofAdd z))) =
      rootOrbitLineEquiv k L j hG hj hT β r z := by
  change (RelativeRoot.rootPointLieEquiv hT j_L r.val.property.1
      (rootOrbit_hasNoHigherRoots k L f j hS hT ha hhigh β horbit r))
    ((RelativeRoot.rootPointLieEquiv hT j_L r.val.property.1
      (rootOrbit_hasNoHigherRoots k L f j hS hT ha hhigh β horbit r)).symm
        (rootOrbitLineEquiv k L j hG hj hT β r z)) = _
  exact AddEquiv.apply_symm_apply _ _

attribute [local instance] orbitFintype

/-- Extending the actual root-field point is the ordered product of its
split-root points at all conjugate embeddings, in any enumeration. -/
theorem rootOrbitFieldPoint_fieldExtend_eq_product
    {n : ℕ} (e : Fin n ≃ MulAction.orbit (L ≃ₐ[k] L) β)
    (x : rootOrbitField k L j β) :
    (rootGroupPointsFieldExtend (k := k) (K := L) (S := S) (G := G) i a
      (rootOrbitFieldPoint k L f j hG hj hS hT ha hhigh β horbit x)).val =
      RelativeRoot.rootPointsProduct j_L (fun l => (e l).val.val) (Over.mk (𝟙 _))
        (fun l => rootOrbitPointEquiv k L f j hG hj hS hT ha hhigh β horbit (e l)
          (Multiplicative.ofAdd (rootOrbitEmbeddingEquiv k L j β (e l) x))) := by
  classical
  let X (l : Fin n) : rootGroupPoints (k := L) (S := T_L) (G := G_L) j_L (e l).val.val :=
    rootOrbitPointEquiv k L f j hG hj hS hT ha hhigh β horbit (e l)
      (Multiplicative.ofAdd (rootOrbitEmbeddingEquiv k L j β (e l) x))
  let q := CommGroupScheme.groupHom f_L ≫ j_L
  have haL : (a_L a) ≠ 0 := (characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha
  have hhL : RelativeRoot.HasNoHigherRoots q (a_L a) := by
    have hh := RelativeRoot.HasNoHigherRoots.baseChange (k := k) (K := L)
      (S := S) (G := G) (a := a) hS i hhigh
    rw [Functor.map_comp] at hh
    exact hh
  let R := RelativeRoot.rootPointLieEquiv (k := L) (S := S_L) (G := G_L)
    (a := a_L a) (hS.baseChange b) q haL hhL
  let y : rootGroupPoints (k := L) (S := S_L) (G := G_L) q (a_L a) :=
    ⟨RelativeRoot.rootPointsProduct (k := L) (T := T_L) (G := G_L)
      j_L (fun l : Fin n => (e l).val.val) (Over.mk (𝟙 _)) X, by
      apply Subgroup.list_prod_mem
      intro g hg
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hg
      have hmem := (RelativeRoot.rootGroupPointsTorusInclusion
        (S := S_L) (T := T_L) (G := G_L) f_L j_L (e l).val.val (X l)).property
      change (X l).val ∈ _ at hmem
      rw [rootOrbit_restriction k L f j β horbit (e l)] at hmem
      exact hmem⟩
  let z : rootGroupPoints (k := L) (S := S_L) (G := G_L) q (a_L a) :=
    ⟨GaloisPointComparison.rationalExtend k L G
      (rootOrbitFieldPoint k L f j hG hj hS hT ha hhigh β horbit x).val, by
      have hmem := rationalExtend_mem_rootGroupPoints
        (k := k) (K := L) i a
        (rootOrbitFieldPoint k L f j hG hj hS hT ha hhigh β horbit x).property
      rw [Functor.map_comp] at hmem
      exact hmem⟩
  have hz : (R (Additive.ofMul z) : Additive (lieKernel G_L L)) =
      (rootOrbitFieldFixedSpanEquiv k L j hG hj hT β x).val.val := by
    have hq : i_L = q := (GroupScheme.baseChange b).map_comp (CommGroupScheme.groupHom f) j
    have hc := RelativeRoot.rootPointLieEquiv_congr (k := L) (S := S_L) (G := G_L)
      (hS.baseChange b) hq haL
      (RelativeRoot.HasNoHigherRoots.baseChange (k := k) (K := L)
        (S := S) (G := G) (a := a) hS i hhigh) hhL
      (rootGroupPointsFieldExtend (k := k) (K := L) (S := S) (G := G) i a
        (rootOrbitFieldPoint k L f j hG hj hS hT ha hhigh β horbit x)) z rfl
    exact hc.symm.trans
      (rootOrbitFieldPoint_extendedLie k L f j hG hj hS hT ha hhigh β horbit x)
  have hy : (R (Additive.ofMul y) : Additive (lieKernel G_L L)) =
      ∑ l, ((rootOrbitLineEquiv k L j hG hj hT β (e l)
        (rootOrbitEmbeddingEquiv k L j β (e l) x)) : Additive (lieKernel G_L L)) := by
    have hprod := RelativeRoot.rootPointLieEquiv_rootPointsProduct
      (k := L) (S := S_L) (T := T_L) (G := G_L)
      (hS.baseChange b) hT f_L j_L haL hhL (fun l => (e l).val.val)
      (fun l => (e l).val.property.1)
      (fun l => rootOrbit_hasNoHigherRoots k L f j hS hT ha hhigh β horbit (e l))
      (fun l => rootOrbit_restriction k L f j β horbit (e l)) X y rfl
    refine hprod.trans (Finset.sum_congr rfl fun l _ => ?_)
    exact congrArg Subtype.val
      (rootOrbitPointEquiv_lie k L f j hG hj hS hT ha hhigh β horbit (e l)
        (rootOrbitEmbeddingEquiv k L j β (e l) x))
  have hsum : (rootOrbitFieldFixedSpanEquiv k L j hG hj hT β x).val.val =
      ∑ l, ((rootOrbitLineEquiv k L j hG hj hT β (e l)
        (rootOrbitEmbeddingEquiv k L j β (e l) x)) : Additive (lieKernel G_L L)) := by
    rw [rootOrbitFieldFixedSpanEquiv_val]
    exact (e.sum_comp _).symm
  have hzy : z = y :=
    Additive.ofMul.injective (R.injective (Subtype.ext (hz.trans (hsum.trans hy.symm))))
  exact congrArg Subtype.val hzy

end Langlands.Geometry.Building
