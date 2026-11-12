import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineEmbedding
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation

/-!
# Equalizer loci of lifted points of the Galois-twisted line

Let `x y` be points of the Galois-twisted line over a scheme `W` that lift to points `τ₁ τ₂` of
the line. Then the locus of `W` where `x` and `y` agree is the base change of the relation
`R → U ×_K U` along `(τ₁, τ₂)`. It is a monomorphism, an immersion and affine.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

open RelationQuotient KernelPair

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')
variable {W : Over (Spec (CommRingCat.of K))} (τ₁ τ₂ : W ⟶ lineOver K K')

/-- The base change of the relation along a pair of points of the line. -/
abbrev liftLocus : Over (Spec (CommRingCat.of K)) :=
  Limits.pullback (prod.lift τ₁ τ₂) (prod.lift (tOver D) (sOver D))

/-- The inclusion of the locus. -/
abbrev liftLocusι : liftLocus D τ₁ τ₂ ⟶ W := Limits.pullback.fst _ _

theorem liftLocus_w₁ : liftLocusι D τ₁ τ₂ ≫ τ₁ = Limits.pullback.snd _ _ ≫ tOver D := by
  simpa using congrArg (· ≫ prod.fst) (Limits.pullback.condition (f := prod.lift τ₁ τ₂)
    (g := prod.lift (tOver D) (sOver D)))

theorem liftLocus_w₂ : liftLocusι D τ₁ τ₂ ≫ τ₂ = Limits.pullback.snd _ _ ≫ sOver D := by
  simpa using congrArg (· ≫ prod.snd) (Limits.pullback.condition (f := prod.lift τ₁ τ₂)
    (g := prod.lift (tOver D) (sOver D)))

theorem atlas_app_comp {T T' : Over (Spec (CommRingCat.of K))} (k : T' ⟶ T)
    (τ : T ⟶ lineOver K K') :
    (atlas D).app (op T') ⟨k ≫ τ⟩ = (space D).presheaf.map k.op ((atlas D).app (op T) ⟨τ⟩) :=
  NatTrans.naturality_apply (atlas D) k.op ⟨τ⟩

theorem atlas_app_t_eq_s {T : Over (Spec (CommRingCat.of K))} (k : T ⟶ relOver D) :
    (atlas D).app (op T) ⟨k ≫ tOver D⟩ = (atlas D).app (op T) ⟨k ≫ sOver D⟩ :=
  congrArg (fun φ => φ.app _ ⟨k⟩) (isPullback_atlas D).w

/-- **The locus represents the equalizer.** -/
theorem representsEqualizer_liftLocus (x y : (space D).presheaf.obj (op W))
    (h₁ : (atlas D).app (op W) ⟨τ₁⟩ = x) (h₂ : (atlas D).app (op W) ⟨τ₂⟩ = y) :
    RepresentsEqualizer (F := (space D).presheaf) (liftLocusι D τ₁ τ₂) x y := by
  intro T g
  constructor
  · rintro ⟨z, rfl⟩
    rw [← h₁, ← h₂, ← atlas_app_comp, ← atlas_app_comp, Category.assoc, Category.assoc,
      liftLocus_w₁, liftLocus_w₂, ← Category.assoc, ← Category.assoc, atlas_app_t_eq_s]
  · intro hg
    rw [← h₁, ← h₂, ← atlas_app_comp, ← atlas_app_comp] at hg
    obtain ⟨r, hr₁, hr₂⟩ := EtaleEquivalenceRelation.exists_lift_of_isPullback
      (isPullback_atlas D) (g ≫ τ₁) (g ≫ τ₂) (map_comp_eq_of_app_eq (atlas D) hg)
    exact ⟨Limits.pullback.lift g r (by apply prod.hom_ext <;> simp [hr₁, hr₂]),
      Limits.pullback.lift_fst _ _ _⟩

theorem mono_liftLocusι : Mono (liftLocusι D τ₁ τ₂).left := by
  have : Mono (prod.lift (tOver D) (sOver D)) :=
    mono_prodLift_of_isPullback (atlas D) (isPullback_atlas D)
  have : Mono (liftLocusι D τ₁ τ₂) := inferInstance
  infer_instance

theorem isPullback_liftLocus_left :
    IsPullback (liftLocusι D τ₁ τ₂).left (Limits.pullback.snd (prod.lift τ₁ τ₂)
      (prod.lift (tOver D) (sOver D))).left (prod.lift τ₁ τ₂).left
      (prod.lift (tOver D) (sOver D)).left :=
  (IsPullback.of_hasPullback _ _).map (Over.forget _)

theorem isImmersion_liftLocusι : IsImmersion (liftLocusι D τ₁ τ₂).left := by
  have := isImmersion_prodLift D
  exact MorphismProperty.of_isPullback (P := @IsImmersion) (isPullback_liftLocus_left D τ₁ τ₂).flip
    inferInstance

theorem isAffineHom_liftLocusι : IsAffineHom (liftLocusι D τ₁ τ₂).left := by
  have := isAffineHom_prodLift D
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_liftLocus_left D τ₁ τ₂).flip
    inferInstance

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
