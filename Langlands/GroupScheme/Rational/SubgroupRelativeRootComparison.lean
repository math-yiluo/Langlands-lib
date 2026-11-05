import Langlands.GroupScheme.Rational.SubgroupRelativeRoots
import Langlands.GroupScheme.Rational.RootSignParabolicLie

/-! # Actual relative roots of monomorphic subgroup representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    (a : T.toGrp ⟶ H) (p : H ⟶ G)

omit [IsAffineHom H.X.hom] [IsAffineHom G.X.hom] in
/-- Conjugation along the source torus map is equivariant for every actual
group-scheme homomorphism. -/
theorem conjugation_act_comp (U : Over (Spec (CommRingCat.of k)))
    (t : U ⟶ T.X) (x : U ⟶ H.X) :
    (AutomorphicAction.conjugation a).act t x ≫ p.hom.hom =
      (AutomorphicAction.conjugation (a ≫ p)).act t (x ≫ p.hom.hom) := by
  simp only [AutomorphicAction.conjugation_act, MonObj.mul_comp, GrpObj.inv_comp,
    Grp.comp_hom_hom, Category.assoc]

variable [Mono p.hom.hom]

/-- Intrinsic source roots coincide with ambient nonzero weights supported by
the image of a monomorphic subgroup homomorphism. -/
theorem relativeRoots_eq_subgroupRelativeRoots_range :
    relativeRoots a = subgroupRelativeRoots (a ≫ p) (SubgroupFunctor.range p) := by
  ext α
  rw [mem_relativeRoots, mem_subgroupRelativeRoots,
    mem_actionWeightSupport_range_iff
      (AutomorphicAction.conjugation (a ≫ p)) (AutomorphicAction.conjugation a)
      p (conjugation_act_comp a p),
    actionWeightSpace_conjugation]
  exact and_comm

/-- The identity on characters identifies the actual roots of a subgroup
representative with its ambient supported roots. -/
def relativeRootsEquivSubgroupRelativeRoots :
    relativeRoots a ≃ subgroupRelativeRoots (a ≫ p) (SubgroupFunctor.range p) where
  toFun α := ⟨α.val, (relativeRoots_eq_subgroupRelativeRoots_range a p) ▸ α.property⟩
  invFun α := ⟨α.val, (relativeRoots_eq_subgroupRelativeRoots_range a p).symm ▸ α.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem relativeRootsEquivSubgroupRelativeRoots_apply
    (α : relativeRoots a) :
    (relativeRootsEquivSubgroupRelativeRoots a p α : characterLattice T) = α := rfl

/-- A torus lift through a monomorphic representative identifies its intrinsic
relative roots with the ambient subgroup's supported roots. -/
theorem relativeRoots_eq_subgroupRelativeRoots_of_lift
    (i : T.toGrp ⟶ G) (ha : a ≫ p = i) :
    relativeRoots a = subgroupRelativeRoots i (SubgroupFunctor.range p) := by
  rw [relativeRoots_eq_subgroupRelativeRoots_range a p, ha]

section Parabolic

variable [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

include hT

omit [IsAffineHom H.X.hom] [Mono p.hom.hom] in
/-- The actual roots supported by a dynamic parabolic are precisely the
ambient roots with nonnegative cocharacter pairing. -/
theorem subgroupRelativeRoots_dynamicParabolic :
    subgroupRelativeRoots i (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) =
      {α | α ∈ relativeRoots i ∧ 0 ≤ latticePairing T α ν} := by
  have hLie := (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
    (tangentSubmodule_parabolic_eq_semigroupWeightSpan hT i ν)
  ext α
  rw [mem_subgroupRelativeRoots,
    HasLieImage.mem_actionWeightSupport_iff
      (AutomorphicAction.conjugation i) hT (nonnegativeSemigroup ν) hLie α,
    actionWeightSpace_conjugation]
  change ((0 ≤ latticePairing T α ν ∧ weightSpace i α ≠ ⊥) ∧ α ≠ 0) ↔
    ((α ≠ 0 ∧ weightSpace i α ≠ ⊥) ∧ 0 ≤ latticePairing T α ν)
  tauto

omit [IsAffineHom H.X.hom] [Mono p.hom.hom] in
/-- Genericity removes the zero-pairing case from the parabolic's actual roots. -/
theorem subgroupRelativeRoots_dynamicParabolic_of_generic
    (hν : IsGenericCocharacter i ν) :
    subgroupRelativeRoots i (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) =
      positiveRelativeRoots i ν := by
  rw [subgroupRelativeRoots_dynamicParabolic hT i ν]
  ext α
  change (α ∈ relativeRoots i ∧ 0 ≤ latticePairing T α ν) ↔
    (α ∈ relativeRoots i ∧ 0 < latticePairing T α ν)
  constructor
  · rintro ⟨hα, hpair⟩
    have hne := hν α hα
    exact ⟨hα, by omega⟩
  · rintro ⟨hα, hpair⟩
    exact ⟨hα, le_of_lt hpair⟩

omit [Mono p.hom.hom] in
/-- Any affine representative of a generic dynamic parabolic has exactly the
positive ambient relative roots, for the actual lifted torus. -/
theorem relativeRoots_parabolicRepresentative_of_generic
    (hp : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy p)
    (ha : a ≫ p = i) (hν : IsGenericCocharacter i ν) :
    relativeRoots a = positiveRelativeRoots i ν := by
  have : Mono p.hom.hom := hp.1
  rw [relativeRoots_eq_subgroupRelativeRoots_of_lift a p i ha, hp.2]
  exact subgroupRelativeRoots_dynamicParabolic_of_generic hT i ν hν

end Parabolic

end Langlands.GroupScheme.RelativeRoot
