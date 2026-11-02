import Langlands.AlgebraicGeometry.GroupoidCoactionRelation
import Langlands.AlgebraicGeometry.GroupoidCoactionCounitEquivalence
import Mathlib.Algebra.Category.Ring.Constructions

/-! # The relation ring as the tensor square over the invariant ring -/

universe u

open TensorProduct CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

/-- The target map, viewed over the equalizer of the source and target maps. -/
def invariantTargetAlgHom (t : B →+* C) : B →ₐ[invariantRing t] C where
  toRingHom := t
  commutes' a := a.property

/-- The canonical map from the invariant-ring tensor square to the relation ring. -/
def relationTensorHom (t : B →+* C) : B ⊗[invariantRing t] B →ₐ[B] C :=
  Algebra.TensorProduct.lift (Algebra.ofId B C) (invariantTargetAlgHom t)
    (fun _ _ => Commute.all _ _)

@[simp]
lemma relationTensorHom_tmul (b b' : B) :
    relationTensorHom t (b ⊗ₜ[invariantRing t] b') = algebraMap B C b * t b' :=
  rfl

variable (hE : RingEtaleEquivalenceRelation t)
variable (hacyclic : ∀ (K : Type u) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), θK.IsAcyclic)
variable (hdetect : ∀ (K : Type u) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), Subsingleton θK.invariantSubmodule → Subsingleton K)

include hE hacyclic hdetect in
lemma relationTensorHom_bijective : Function.Bijective (relationTensorHom t) := by
  let e : B ⊗[invariantRing t] B ≃ₗ[B] C :=
    ((relationInvariantEquiv hE).baseChange (invariantRing t) B).trans
      (invariantCounitLinearEquiv hE hacyclic hdetect (relation hE))
  have he : (relationTensorHom t).toLinearMap = e.toLinearMap := by
    apply AlgebraTensorModule.ext
    intro b b'
    simp [e, Algebra.smul_def]
  change Function.Bijective (relationTensorHom t).toLinearMap
  rw [he]
  exact e.bijective

/-- The canonical algebra equivalence from the tensor square to the relation ring. -/
noncomputable def relationTensorEquiv : B ⊗[invariantRing t] B ≃ₐ[B] C :=
  AlgEquiv.ofBijective (relationTensorHom t)
    (relationTensorHom_bijective hE hacyclic hdetect)

@[simp]
lemma relationTensorEquiv_tmul (b b' : B) :
    relationTensorEquiv hE hacyclic hdetect (b ⊗ₜ[invariantRing t] b') =
      algebraMap B C b * t b' :=
  rfl

include hE hacyclic hdetect in
/-- The two relation maps form the pushout of the equalizer-ring inclusion with itself. -/
lemma isPushout_invariantRing :
    IsPushout (CommRingCat.ofHom (algebraMap (invariantRing t) B))
      (CommRingCat.ofHom (algebraMap (invariantRing t) B))
      (CommRingCat.ofHom t) (CommRingCat.ofHom (algebraMap B C)) := by
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap (invariantRing t) B))
      (CommRingCat.ofHom (algebraMap (invariantRing t) B))
      (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom t) := by
    refine (CommRingCat.isPushout_tensorProduct (invariantRing t) B B).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (relationTensorEquiv hE hacyclic hdetect).toRingEquiv.toCommRingCatIso
      (by simp) (by simp) ?_ ?_
    · ext b
      change relationTensorEquiv hE hacyclic hdetect (b ⊗ₜ[invariantRing t] (1 : B)) =
        algebraMap B C b
      simp
    · ext b
      change relationTensorEquiv hE hacyclic hdetect ((1 : B) ⊗ₜ[invariantRing t] b) = t b
      simp
  exact hpo.flip

end Langlands.AlgebraicGeometry.GroupoidCoaction
