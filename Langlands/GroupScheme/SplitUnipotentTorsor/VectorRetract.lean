import Langlands.GroupScheme.SplitUnipotentTorsor.VectorCocycle
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Descent

/-! # Affine cocycles and torsors under retracts of finite vector groups

A retract is witnessed by actual group-scheme homomorphisms. Additive Amitsur exactness
trivializes finite-dimensional vector-group cocycles coordinate by coordinate, and a
retraction transports the resulting coboundary back to the original group.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot Langlands.AlgebraicGeometry.AffineAdditiveCocycle

variable {B : Scheme.{u}}

/-- An actual group scheme is a retract of a finite vector group when there are
group-scheme homomorphisms into and out of such a vector group whose composite is
the identity. This is sufficient retraction data, not a definition of a vector bundle. -/
def IsFiniteVectorGroupRetract (V : GroupScheme B) : Prop :=
  ∃ (n : ℕ) (W : GroupScheme B) (j : V ⟶ W) (p : W ⟶ V),
    IsVectorGroupOfDimension W n ∧ j ≫ p = 𝟙 V

namespace Cocycle

variable {V W : GroupScheme B} {U : Over B}

/-- Triviality of a cocycle can be transported back along an actual retraction. -/
theorem IsTrivial.of_map_retract {ξ : Cocycle V U} (j : V ⟶ W) (p : W ⟶ V)
    (hjp : j ≫ p = 𝟙 V) (hξ : (ξ.map j).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f, hf⟩ := hξ
  refine ⟨f ≫ p.hom.hom, fun {Z} a b => ?_⟩
  have h := congrArg (fun x : Z ⟶ W.X => x ≫ p.hom.hom) (hf a b)
  change (ξ.toFun a b ≫ j.hom.hom) ≫ p.hom.hom = _ at h
  have hjp' : j.hom.hom ≫ p.hom.hom = 𝟙 V.X :=
    congrArg (fun q : V ⟶ V => q.hom.hom) hjp
  simpa only [Category.assoc, hjp', Category.comp_id, MonObj.mul_comp,
    GrpObj.inv_comp] using h

/-- Over an affine scheme every cocycle of a finite-dimensional vector group on an
affine flat surjective cover is trivial, including dimension zero. -/
theorem isTrivial_of_isVectorGroupOfDimension {n : ℕ}
    (hV : IsVectorGroupOfDimension V n)
    (T : Over B) [IsAffine T.left] (U : Over T.left) [IsAffine U.left] [Flat U.hom]
    [Surjective U.hom] (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj V) U) :
    ξ.IsTrivial := by
  obtain ⟨e, he⟩ := hV
  let coord := VectorCocycle.baseChangeCoordinates e T
  have hcoord := @VectorCocycle.baseChangeCoordinates_comp _ _ _ e T he
  let α (j : Fin n) : AddCocycle U :=
    { toFun := fun a b => (coord _ (ξ.toFun a b)).toAdd j
      naturality := fun t a b => by
        simp only [coord]
        rw [ξ.naturality, hcoord]
      cocycle := fun a b c => by
        simp only [coord]
        rw [ξ.cocycle a b c, map_mul, toAdd_mul, Pi.add_apply] }
  choose β hβ using fun j => (α j).exists_coboundary
  refine ⟨(coord U).symm (Multiplicative.ofAdd fun j => β j), fun {Z} a b => ?_⟩
  apply (coord Z).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply,
    hcoord, hcoord, MulEquiv.apply_symm_apply, toAdd_ofAdd, ← sub_eq_add_neg]
  exact hβ j a b

/-- The affine cocycle vanishing property passes to every actual group-scheme retract
of a finite-dimensional vector group. -/
theorem isTrivial_of_isFiniteVectorGroupRetract
    (hV : IsFiniteVectorGroupRetract V)
    (T : Over B) [IsAffine T.left] (U : Over T.left) [IsAffine U.left] [Flat U.hom]
    [Surjective U.hom] (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj V) U) :
    ξ.IsTrivial := by
  obtain ⟨n, W, j, p, hW, hjp⟩ := hV
  apply IsTrivial.of_map_retract ((GroupScheme.baseChange T.hom).map j)
    ((GroupScheme.baseChange T.hom).map p)
  · rw [← Functor.map_comp, hjp]
    exact (GroupScheme.baseChange T.hom).map_id V
  · exact isTrivial_of_isVectorGroupOfDimension hW T U _

end Cocycle

/-- Every fpqc torsor under a retract of a finite vector group has a section over an
affine test scheme. No affine, smooth or connectedness hypotheses on its total space
are required. -/
theorem exists_section_of_isFiniteVectorGroupRetract {V : GroupScheme B}
    (hV : IsFiniteVectorGroupRetract V)
    (T : Over B) [IsAffine T.left] (X : Over T.left)
    [ModObj ((GroupScheme.baseChange T.hom).obj V).X X] (hflat : Flat X.hom)
    (hsurj : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hX : IsIso (ModObj.leftSMul ((GroupScheme.baseChange T.hom).obj V).X X)) :
    ∃ s : T.left ⟶ X.left, s ≫ X.hom = 𝟙 T.left := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities @Flat := ⟨fun Y => (inferInstance : Flat (𝟙 Y))⟩
  obtain ⟨W, p, hp, hpf, hW⟩ := X.left.exists_hom_isAffine_of_isZariskiLocalAtSource @Flat
  let U : Over T.left := Over.mk (p ≫ X.hom)
  have : IsAffine U.left := hW
  have : Flat U.hom := Flat.comp p X.hom
  have : Surjective U.hom := (inferInstance : Surjective (p ≫ X.hom))
  have : EffectiveEpi U.hom := (inferInstance : EffectiveEpi (p ≫ X.hom))
  exact exists_section_of_isTrivial hX (Over.homMk p rfl : U ⟶ X)
    (Cocycle.isTrivial_of_isFiniteVectorGroupRetract hV T U _)

end Langlands.GroupScheme
