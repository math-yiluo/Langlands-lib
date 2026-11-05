import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Algebraic bounds under polynomial evaluation and closed immersions -/

noncomputable section

universe u v w

open CategoryTheory ValuativeRel
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section Evaluation

variable {F : Type u} [Field F] [ValuativeRel F]
  {A : Type v} [CommRing A] [Algebra F A]
  {ι : Type w} (e : ι → A →ₐ[F] F)

/-- Elements with uniformly bounded evaluations form a subalgebra. -/
def boundedEvaluationSubalgebra : Subalgebra F A where
  carrier := {a | ∃ b : F, b ≠ 0 ∧ ∀ i, e i a ≤ᵥ b}
  algebraMap_mem' c := by
    by_cases hc : c = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      intro i
      simp [hc, zero_vle]
    · exact ⟨c, hc, fun i => by simp⟩
  zero_mem' := ⟨1, one_ne_zero, fun i => by simp [zero_vle]⟩
  one_mem' := ⟨1, one_ne_zero, fun i => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    rcases vle_total c d with h | h
    · exact ⟨d, hd, fun i => by
        simpa only [map_add] using vle_add ((ha i).trans h) (hb i)⟩
    · exact ⟨c, hc, fun i => by
        simpa only [map_add] using vle_add (ha i) ((hb i).trans h)⟩
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c * d, mul_ne_zero hc hd, fun i => by
      simpa only [map_mul] using ValuativeRel.mul_vle_mul (ha i) (hb i)⟩

/-- Uniform bounds on polynomial generators bound every polynomial separately. -/
theorem boundedEvaluation_polynomial {σ : Type*}
    (f : MvPolynomial σ F →ₐ[F] A)
    (hX : ∀ s, f (MvPolynomial.X s) ∈ boundedEvaluationSubalgebra e)
    (p : MvPolynomial σ F) :
    f p ∈ boundedEvaluationSubalgebra e := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa only [MvPolynomial.C_eq_algebraMap, AlgHom.commutes] using
        (boundedEvaluationSubalgebra e).algebraMap_mem c
  | add p q hp hq =>
      simpa only [map_add] using (boundedEvaluationSubalgebra e).add_mem hp hq
  | mul_X p s hp =>
      simpa only [map_mul] using (boundedEvaluationSubalgebra e).mul_mem hp (hX s)

/-- A surjective polynomial presentation reduces boundedness to its generators. -/
theorem boundedEvaluation_of_polynomial_surjective {σ : Type*}
    (f : MvPolynomial σ F →ₐ[F] A) (hf : Function.Surjective f)
    (hX : ∀ s, f (MvPolynomial.X s) ∈ boundedEvaluationSubalgebra e)
    (a : A) : ∃ b : F, b ≠ 0 ∧ ∀ i, e i a ≤ᵥ b := by
  obtain ⟨p, rfl⟩ := hf a
  exact boundedEvaluation_polynomial e f hX p

end Evaluation

section Schemes

variable (F : Type u) [Field F]
  {X Y : Over (Spec (CommRingCat.of F))} [IsAffine X.left] [IsAffine Y.left]

/-- Evaluation is actual global-section pullback followed by the spectrum
global-section comparison. -/
theorem rationalPointAlgebraHom_apply_appTop (p : RationalPoint F X)
    (a : AffineCoordinateRing F X) :
    rationalPointAlgebraHom F X p a =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom (p.left.appTop a) := by
  let : IsAffine (Over.mk (𝟙 (Spec (CommRingCat.of F)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
  have h : CommRingCat.ofHom (rationalPointAlgebraHom F X p).toRingHom =
      p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom
      (affineSchemePointEquiv F X F (rationalPointEquiv F X p)).toAlgHom.toRingHom) = _
    rw [affineSchemePointEquiv_spec]
    rw [rationalPointEquiv_left]
    have hn : p.left ≫ X.left.isoSpec.hom =
        (Spec (CommRingCat.of F)).isoSpec.hom ≫ Spec.map p.left.appTop :=
      (Scheme.isoSpec_hom_naturality p.left).symm
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp] at hn
    exact hn
  exact congrArg (fun f : CommRingCat.of (AffineCoordinateRing F X) ⟶
    CommRingCat.of F => f a) h

/-- Evaluation commutes with the actual global-section pullback. -/
theorem rationalPointAlgebraHom_pullback (f : X ⟶ Y) (p : RationalPoint F X)
    (a : AffineCoordinateRing F Y) :
    rationalPointAlgebraHom F X p (affineCoordinatePullback F f a) =
      rationalPointAlgebraHom F Y (p ≫ f) a := by
  rw [rationalPointAlgebraHom_apply_appTop, rationalPointAlgebraHom_apply_appTop]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of F)).hom ((p.left ≫ f.left).appTop a)
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- A surjective pullback transports algebraic bounds to the source. -/
theorem isAlgebraicallyBounded_of_pullback_surjective [ValuativeRel F]
    (f : X ⟶ Y) (hf : Function.Surjective (affineCoordinatePullback F f))
    (B : Set (RationalPoint F X))
    (hB : IsAlgebraicallyBounded F Y ((fun p => p ≫ f) '' B)) :
    IsAlgebraicallyBounded F X B := by
  intro a
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, hb, h⟩ := hB a
  refine ⟨b, hb, fun p hp => ?_⟩
  rw [rationalPointAlgebraHom_pullback]
  exact h (p ≫ f) ⟨p, hp, rfl⟩

/-- Closed immersions of affine schemes reflect algebraic boundedness. -/
theorem isAlgebraicallyBounded_of_closedImmersion [ValuativeRel F]
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    (B : Set (RationalPoint F X))
    (hB : IsAlgebraicallyBounded F Y ((fun p => p ≫ f) '' B)) :
    IsAlgebraicallyBounded F X B :=
  isAlgebraicallyBounded_of_pullback_surjective F f
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2 B hB

end Schemes

end Langlands.AlgebraicGeometry.PointTopology
