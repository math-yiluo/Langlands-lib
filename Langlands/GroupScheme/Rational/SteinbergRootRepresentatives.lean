import Langlands.GroupScheme.Rational.SteinbergCanonicalGaloisTransport

/-! # Canonical reflection points for arbitrary parametrized roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 400000

section Root

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {α : p.rootIndex}

local instance : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1

namespace RootParametrization

variable (x : p.RootParametrization α)

/-- Coordinate one in the supplied root parametrization, without a Lie normalization. -/
def unitPoint : rationalPoints G := x.rationalPoint 1

theorem rationalPoint_mem (c : k) :
    x.rationalPoint c ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier (Over.mk (𝟙 _)) :=
  (x.mem_rootSubgroup_iff _ _).mpr ⟨_, rfl⟩

theorem unitPoint_mem :
    x.unitPoint ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier (Over.mk (𝟙 _)) :=
  x.rationalPoint_mem 1

theorem unitPoint_ne_one : x.unitPoint ≠ 1 :=
  x.rationalPoint_ne_one one_ne_zero

/-- The unique ordered normalizing opposite pair around coordinate one. -/
def oppositeFactorPair : rationalPoints G × rationalPoints G :=
  Classical.choose (splitPinnedOppositeFactorPairs k G p (p.rootDatum.root α)
    (p.root_mem_relativeRoots α) x.unitPoint x.unitPoint_mem x.unitPoint_ne_one)

theorem oppositeFactorPair_spec :
    RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root α)
      x.unitPoint x.oppositeFactorPair :=
  Classical.choose_spec (splitPinnedOppositeFactorPairs k G p (p.rootDatum.root α)
    (p.root_mem_relativeRoots α) x.unitPoint x.unitPoint_mem x.unitPoint_ne_one)

theorem eq_oppositeFactorPair {q : rationalPoints G × rationalPoints G}
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root α)
      x.unitPoint q) : q = x.oppositeFactorPair :=
  hq.eq p.inclusion p.isSplitTorus (p.root_mem_relativeRoots α).1
    x.unitPoint_mem x.unitPoint_ne_one x.oppositeFactorPair_spec

/-- A root-generated point realizing the reflection in the parametrized root. -/
def reflectionRepresentative : p.ReflectionRepresentative α :=
  let n : normalizerPoints p.inclusion :=
    ⟨x.oppositeFactorPair.1 * x.unitPoint * x.oppositeFactorPair.2,
      x.oppositeFactorPair_spec.2.2⟩
  { point := n.val
    torusAut := normalizingAut p.inclusion n
    normalizes := isNormalizingPoint_normalizingAut p.inclusion n
    characterAut_eq := p.oppositeFactorPair_weylAction α
      x.unitPoint_mem x.unitPoint_ne_one x.oppositeFactorPair_spec }

theorem reflectionRepresentative_point :
    x.reflectionRepresentative.point =
      x.oppositeFactorPair.1 * x.unitPoint * x.oppositeFactorPair.2 := rfl

theorem reflectionRepresentative_mem_generated :
    x.reflectionRepresentative.point ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion (-(p.rootDatum.root α))).carrier
          (Over.mk (𝟙 _)) :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mem_sup_right x.oppositeFactorPair_spec.1)
      (Subgroup.mem_sup_left x.unitPoint_mem))
    (Subgroup.mem_sup_right x.oppositeFactorPair_spec.2.1)

end RootParametrization

namespace NormalizedRootParametrization

variable {a : p.base.support} (x : p.NormalizedRootParametrization a)

@[simp] theorem toRootParametrization_unitPoint :
    x.toRootParametrization.unitPoint = x.unitPoint := rfl

@[simp] theorem toRootParametrization_oppositeFactorPair :
    x.toRootParametrization.oppositeFactorPair = x.oppositeFactorPair := rfl

@[simp] theorem toRootParametrization_reflectionRepresentative_point :
    x.toRootParametrization.reflectionRepresentative.point = x.reflectionRepresentative.point :=
  rfl

end NormalizedRootParametrization

end Root

section Galois

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)

namespace RootParametrization

variable {α β : p.rootIndex} (x : p.RootParametrization α) (y : p.RootParametrization β)
    (σ : K ≃ₐ[k] K)
    (hroot : characterLattice.congr eT (p.rootDatum.root β) =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.congr eT (p.rootDatum.root α)))
    (hunit : rationalConjugate k K G σ x.unitPoint = y.unitPoint)

include hT hroot hunit

/-- Transport of the root and its coordinate-one point transports the unique opposite pair. -/
theorem oppositeFactorPair_rationalConjugate :
    (rationalConjugate k K G σ x.oppositeFactorPair.1,
      rationalConjugate k K G σ x.oppositeFactorPair.2) = y.oppositeFactorPair := by
  have hx := x.oppositeFactorPair_spec.changeTorus eT hT
  have hq := hx.rationalConjugate k K i σ
  rw [← hroot, hunit] at hq
  exact y.eq_oppositeFactorPair
    ((RelativeRoot.isOppositeFactorPair_changeTorus_iff eT hT).mp hq)

/-- A compatible parametrized root has a compatible root-generated reflection point. -/
theorem reflectionRepresentative_rationalConjugate :
    rationalConjugate k K G σ x.reflectionRepresentative.point =
      y.reflectionRepresentative.point := by
  have hq := oppositeFactorPair_rationalConjugate k K i p eT hT x y σ hroot hunit
  have hq1 : rationalConjugate k K G σ x.oppositeFactorPair.1 =
      y.oppositeFactorPair.1 := congrArg Prod.fst hq
  have hq2 : rationalConjugate k K G σ x.oppositeFactorPair.2 =
      y.oppositeFactorPair.2 := congrArg Prod.snd hq
  rw [x.reflectionRepresentative_point, y.reflectionRepresentative_point,
    map_mul, map_mul, hunit, hq1, hq2]

end RootParametrization

end Galois

end Langlands.GroupScheme.SplitPinning
