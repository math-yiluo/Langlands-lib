import Langlands.GroupScheme.Rational.RootPointLieNaturality
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.VectorPointLieBaseChange
import Langlands.GroupScheme.Torus.RootSupportBaseChange

/-! # Actual root-point Lie coordinates under field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "U_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) U
local notation "i_K" i => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

/-- Natural coordinates of a single character weight preserve that actual
weight under field extension. -/
theorem IsWeightVectorCoordinates.baseChange
    {c : AutomorphicAction S.toGrp U} {a : characterLattice S} {n : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates c a e) :
    IsWeightVectorCoordinates (c.baseChange b) (a_K a)
      (vectorBaseChangeCoordinates e K) := by
  refine ⟨he.1.baseChange, ?_⟩
  intro T s v
  simp only [vectorBaseChangeCoordinates, MulEquiv.trans_apply,
    AutomorphicAction.baseChangePointsEquiv_act]
  simpa only [Over.map_obj_left, characterValue_baseChange] using
    he.2 ((Over.map b).obj T) (baseChangePointsEquiv b S.toGrp T s)
      (baseChangePointsEquiv b U T v)

/-- The base-changed inclusion represents the actual base-changed root functor. -/
theorem rootSubgroup_isRepresentedBy_baseChange
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j) :
    (subgroup (S := S_K) (i_K i) (a_K a)).IsRepresentedBy (i_K j) := by
  rw [subgroup_baseChange]
  exact hj.baseChange b

/-- Actual conjugation actions on root representatives agree under the
scheme-pullback point comparison. -/
theorem subgroupAction_baseChangePointsEquiv_act
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ (S_K).X) (v : T ⟶ (U_K).X) :
    baseChangePointsEquiv b U T
        ((subgroupAction (S := S_K) (i_K i) (a_K a) (i_K j)
          (rootSubgroup_isRepresentedBy_baseChange i a hj)).act s v) =
      (subgroupAction i a j hj).act
        (baseChangePointsEquiv b S.toGrp T s) (baseChangePointsEquiv b U T v) := by
  let : Mono j.hom.hom := hj.1
  apply (cancel_mono j.hom.hom).mp
  rw [← baseChangePointsEquiv_comp, subgroupAction_act_comp,
    subgroupAction_act_comp, map_mul, map_mul, map_inv,
    baseChangePointsEquiv_comp, baseChangePointsEquiv_comp]

/-- Coordinates of the original root weight remain coordinates of the actual
root action on the pulled-back representative. -/
theorem IsWeightVectorCoordinates.rootBaseChange
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j) {n : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates (subgroupAction i a j hj) a e) :
    IsWeightVectorCoordinates
      (subgroupAction (S := S_K) (i_K i) (a_K a) (i_K j)
        (rootSubgroup_isRepresentedBy_baseChange i a hj))
      (a_K a) (vectorBaseChangeCoordinates e K) := by
  refine ⟨he.1.baseChange, ?_⟩
  intro T s v
  simp only [vectorBaseChangeCoordinates, MulEquiv.trans_apply]
  rw [subgroupAction_baseChangePointsEquiv_act i a hj]
  simpa only [Over.map_obj_left, characterValue_baseChange] using
    he.2 ((Over.map b).obj T) (baseChangePointsEquiv b S.toGrp T s)
      (baseChangePointsEquiv b U T v)

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

local instance {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b)
  infer_instance

local instance : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Absence of higher positive roots is preserved by field extension. -/
theorem HasNoHigherRoots.baseChange
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (hhigh : HasNoHigherRoots i a) :
    HasNoHigherRoots (T := S_K) (i_K i) (a_K a) := by
  intro n hn hroot
  apply hhigh n hn
  apply (mem_roots_baseChange_iff (K := K) G S hS i (n • a)).mp
  simpa only [map_nsmul, relativeRoots_eq_roots] using hroot

variable [IsAffineHom U.X.hom]

/-- Independently chosen weight coordinates on an actual root representative
after field extension give the same point-to-Lie map as transported coordinates. -/
theorem rootVectorPointLieEquiv_baseChange
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (v : Lie.AffinePoints U_K A) :
    let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
    let cK := weightVectorCoordinatesOfNoHigherRoots (T := S_K) (hS.baseChange b) (i_K i)
      ((characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha)
      (hhigh.baseChange hS i) (rootSubgroup_isRepresentedBy_baseChange i a hj)
    Lie.kernelBaseChangeLinearEquiv k K U A
        (vectorPointLieEquiv cK.2.val cK.2.property.1
          (CommAlgCat.of K A) (Additive.ofMul v)) =
      vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k A)
        (Additive.ofMul (Lie.affineBaseChangeEquiv k K U A v)) := by
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  let cK := weightVectorCoordinatesOfNoHigherRoots (T := S_K) (hS.baseChange b) (i_K i)
    ((characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha)
    (hhigh.baseChange hS i) (rootSubgroup_isRepresentedBy_baseChange i a hj)
  have he := c.2.property.rootBaseChange (K := K) i a hj
  change Lie.kernelBaseChangeLinearEquiv k K U A
    (vectorPointLieEquiv cK.2.val cK.2.property.1
      (CommAlgCat.of K A) (Additive.ofMul v)) = _
  rw [vectorPointLieEquiv_eq_of_weight (hS.baseChange b)
    ((characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha)
    cK.2.property he]
  exact vectorPointLieEquiv_baseChange c.2.val c.2.property.1 K A v

/-- The root representative's point-to-Lie equivalence transported through the
actual point and tangent pullback comparisons. -/
def rootVectorPointLieBaseChangeEquiv
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    Additive (Lie.AffinePoints U_K A) ≃+ Additive (lieKernel U_K A) :=
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  vectorPointLieBaseChangeEquiv c.2.val c.2.property.1 K A

/-- The transported root comparison equals the independently constructed
comparison over the extended field. -/
theorem rootVectorPointLieBaseChangeEquiv_eq
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    let cK := weightVectorCoordinatesOfNoHigherRoots (T := S_K) (hS.baseChange b) (i_K i)
      ((characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha)
      (hhigh.baseChange hS i) (rootSubgroup_isRepresentedBy_baseChange i a hj)
    rootVectorPointLieBaseChangeEquiv hS i ha hhigh hj A =
      vectorPointLieEquiv cK.2.val cK.2.property.1 (CommAlgCat.of K A) := by
  apply AddEquiv.ext
  intro v
  apply (Lie.kernelBaseChangeLinearEquiv k K U A).injective
  change (Lie.kernelBaseChangeLinearEquiv k K U A)
    ((Lie.kernelBaseChangeLinearEquiv k K U A).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (rootVectorPointLieEquiv_baseChange hS i ha hhigh hj A v.toMul).symm

end Langlands.GroupScheme.RelativeRoot
