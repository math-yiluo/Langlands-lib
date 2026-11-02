import Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
import Langlands.AlgebraicGeometry.Picard.RelativeGeometry

/-! # Uniqueness of relative rigidified isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- If the relative projection is an isomorphism on global functions, the induced relative
section is injective on global functions. -/
lemma relativeSection_appTop_injective
    (hO : ∀ (T : Over S) (U : T.left.Opens), IsIso (((relativeProjection f).app T).app U))
    (T : Over S) : Function.Injective ((relativeSection f ε section_eq).app T).appTop := by
  have : IsIso ((relativeProjection f).app T).appTop := hO T ⊤
  have hcomp : ((relativeProjection f).app T).appTop ≫
      ((relativeSection f ε section_eq).app T).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, relativeSection_projection, Scheme.Hom.id_appTop]
    rfl
  intro a b hab
  obtain ⟨a', rfl⟩ : ∃ a', ((relativeProjection f).app T).appTop a' = a :=
    ⟨(inv ((relativeProjection f).app T).appTop) a, by
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]⟩
  obtain ⟨b', rfl⟩ : ∃ b', ((relativeProjection f).app T).appTop b' = b :=
    ⟨(inv ((relativeProjection f).app T).appTop) b, by
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]⟩
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hcomp] at hab
  simp only [CommRingCat.id_apply] at hab
  rw [hab]

/-- Under the universal structure-sheaf condition, two relative rigidified line bundles have
at most one rigidified isomorphism between them. -/
theorem relative_iso_subsingleton
    (hO : ∀ (T : Over S) (U : T.left.Opens), IsIso (((relativeProjection f).app T).app U))
    (T : Over S) (L M : relative f ε section_eq T) : Subsingleton (L ≅ M) := by
  refine ⟨fun e₁ e₂ ↦ ?_⟩
  have h := endo_eq_id (relativeSection_appTop_injective f ε section_eq hO T) L
    (e₁.hom ≫ e₂.inv)
  ext1
  simpa using congrArg (· ≫ e₂.hom) h

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
