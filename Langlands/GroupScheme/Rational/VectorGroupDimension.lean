import Langlands.GroupScheme.Rational.VectorGroupCoordinates

/-! # Relative dimension and nontriviality of vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The standard polynomial vector group is smooth of its coordinate dimension,
over any commutative base ring. -/
theorem VectorGroup.smoothOfRelativeDimension (R : CommRingCat.{u}) (n : ℕ) :
    SmoothOfRelativeDimension n (VectorGroup.groupScheme R n).X.hom := by
  change SmoothOfRelativeDimension n
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  infer_instance

namespace RelativeRoot

variable {k : Type u} [Field k]
    {V G : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

/-- The coordinate dimension of an actual vector group equals its smooth
relative dimension over the ground field. -/
theorem IsVectorGroupOfDimension.smoothOfRelativeDimension
    (h : IsVectorGroupOfDimension V n) :
    SmoothOfRelativeDimension n V.X.hom := by
  let f := h.iso
  have : IsIso f.hom.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map f.hom))
  have : SmoothOfRelativeDimension n
      (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom :=
    VectorGroup.smoothOfRelativeDimension (CommRingCat.of k) n
  rw [← Over.w f.hom.hom.hom]
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n)
      (f.hom.hom.hom.left ≫ (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom))

/-- Every point of a zero-dimensional vector group is the identity, on every
scheme test. -/
theorem IsVectorGroupOfDimension.eq_one_of_dim_zero
    (h : IsVectorGroupOfDimension V 0)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ V.X) : v = 1 := by
  obtain ⟨e, _⟩ := h
  apply (e T).injective
  apply Multiplicative.toAdd.injective
  funext j
  exact Fin.elim0 j

/-- Any homomorphism from a zero-dimensional vector group has trivial image
on all scheme tests. -/
theorem IsVectorGroupOfDimension.range_eq_bot_of_dim_zero
    (h : IsVectorGroupOfDimension V 0) (i : V ⟶ G) :
    SubgroupFunctor.range i = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  change v ≫ i.hom.hom ∈ (⊥ : Subgroup (T ⟶ G.X))
  rw [Subgroup.mem_bot, h.eq_one_of_dim_zero v, MonObj.one_comp]

/-- Nontriviality of the image of an actual vector group forces a positive
coordinate dimension. No injectivity of the homomorphism is needed. -/
theorem IsVectorGroupOfDimension.pos_of_range_ne_bot
    (h : IsVectorGroupOfDimension V n) {i : V ⟶ G}
    (hi : SubgroupFunctor.range i ≠ ⊥) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  exact hi (h.range_eq_bot_of_dim_zero i)

/-- Points of an actual vector group commute on every scheme test. -/
theorem IsVectorGroupOfDimension.points_commute
    (h : IsVectorGroupOfDimension V n)
    {T : Over (Spec (CommRingCat.of k))} (v w : T ⟶ V.X) : Commute v w := by
  obtain ⟨e, _⟩ := h
  apply (e T).injective
  simp only [map_mul, mul_comm]

/-- The commutative group structure on test points of a vector group, with
the existing group operations. -/
@[instance_reducible]
def IsVectorGroupOfDimension.pointsCommGroup
    (h : IsVectorGroupOfDimension V n)
    (T : Over (Spec (CommRingCat.of k))) : CommGroup (T ⟶ V.X) :=
  { (inferInstance : Group (T ⟶ V.X)) with
    mul_comm := fun v w => h.points_commute v w }

end RelativeRoot
end Langlands.GroupScheme
