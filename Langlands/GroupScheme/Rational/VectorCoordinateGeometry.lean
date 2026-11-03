import Langlands.GroupScheme.Rational.VectorGroupDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Geometry from natural vector coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {R : CommRingCat.{u}} {V : GroupScheme (Spec R)} {n : ℕ}

/-- Natural vector coordinates give an isomorphism with the actual vector group. -/
def vectorCoordinatesIso
    (e : ∀ T : Over (Spec R),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (he : ∀ (T W : Over (Spec R)) (a : W ⟶ T) (v : T ⟶ V.X),
      (e W (a ≫ v)).toAdd = fun i => a.left.appTop ((e T v).toAdd i)) :
    V ≅ VectorGroup.groupScheme R n :=
  isoOfPoints
    (fun T => (e T).trans (VectorGroup.coordinates R n T).symm)
    (by
      intro T W a v
      apply (VectorGroup.coordinates R n W).injective
      apply Multiplicative.toAdd.injective
      simpa only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
        VectorGroup.coordinates_comp] using he T W a v)

/-- Natural vector coordinates imply the exact relative dimension. -/
theorem IsVectorGroupOfDimension.smoothOfRelativeDimension_overRing
    (hV : IsVectorGroupOfDimension V n) :
    SmoothOfRelativeDimension n V.X.hom := by
  obtain ⟨e, he⟩ := hV
  let f := vectorCoordinatesIso e he
  have : IsIso f.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso f)).hom)
  have := VectorGroup.smoothOfRelativeDimension R n
  rw [← Over.w f.hom.hom.hom]
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n)
      (f.hom.hom.hom.left ≫ (VectorGroup.groupScheme R n).X.hom))

/-- Natural vector coordinates imply that the group is affine over the base. -/
theorem IsVectorGroupOfDimension.isAffineHom_overRing
    (hV : IsVectorGroupOfDimension V n) : IsAffineHom V.X.hom := by
  obtain ⟨e, he⟩ := hV
  let f := vectorCoordinatesIso e he
  have : IsIso f.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso f)).hom)
  have : IsAffineHom (VectorGroup.groupScheme R n).X.hom := by
    change IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
    infer_instance
  rw [← Over.w f.hom.hom.hom]
  infer_instance

/-- A nontrivial image excludes dimension zero, using every test's coordinates. -/
theorem IsVectorGroupOfDimension.pos_of_range_ne_bot_overRing {G : GroupScheme (Spec R)}
    (hV : IsVectorGroupOfDimension V n) (z : V ⟶ G)
    (hz : SubgroupFunctor.range z ≠ ⊥) : 0 < n := by
  obtain ⟨e, he⟩ := hV
  by_contra hn
  have hn : n = 0 := by omega
  subst n
  apply hz
  apply SubgroupFunctor.ext
  intro T
  change (SubgroupFunctor.range z).carrier T = ⊥
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hv
  have hx : x = 1 := (e T).injective (Subsingleton.elim _ _)
  change x ≫ z.hom.hom = 1
  rw [hx, MonObj.one_comp]

end Langlands.GroupScheme.RelativeRoot
