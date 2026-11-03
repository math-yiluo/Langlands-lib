import Langlands.AlgebraicGeometry.Picard.AffineIsomSubalgebraDescent
import Langlands.AlgebraicGeometry.Picard.AffineSectionEqualityDescent
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleHomRepresentability

/-! # Finite algebra approximation of actual Picard arrows -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Langlands.AlgebraicGeometry.Picard

namespace PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S)

/-- The actual arrow from an affine algebra test to a fixed affine base. -/
def affineFamilyBaseArrow (A : Type u) [CommRing A] [Algebra R A] :
    (Over.map t).obj (affineBase R A) ⟶ Over.mk t :=
  ((Over.mk t).iteratedSliceBackward.obj (affineBase R A)).hom

/-- Actual isomorphisms between the restrictions of two fixed families. -/
abbrev AffineFamilyArrow
    (L M : PicardGroupoid ((relativeSpace f).obj (Over.mk t)))
    (A : Type u) [CommRing A] [Algebra R A] :=
  ((relative f).map (affineFamilyBaseArrow t A).op.toLoc).toFunctor.obj L ⟶
    ((relative f).map (affineFamilyBaseArrow t A).op.toLoc).toFunctor.obj M

variable (L M : PicardGroupoid ((relativeSpace f).obj (Over.mk t)))

/-- Restriction of an arrow with its ordinary pullback composition comparisons. -/
def affineFamilyArrowRestrict {A : Type u} [CommRing A] [Algebra R A]
    (B : Subalgebra R A) (φ : AffineFamilyArrow f t L M B) :
    AffineFamilyArrow f t L M A :=
  ((relativeIsomPresheaf f L M).map (affineSubalgebraMap B).op
    (ULift.up φ)).down

set_option maxHeartbeats 1000000 in
/-- The restriction uses the coherent actual pullback, as in the published
relative Hom presheaf. -/
lemma affineFamilyArrowRestrict_eq_pullHom
    {A : Type u} [CommRing A] [Algebra R A] (B : Subalgebra R A)
    (φ : AffineFamilyArrow f t L M B) :
    affineFamilyArrowRestrict f t L M B φ =
      pullHom (F := relative f) φ
        ((Over.mk t).iteratedSliceBackward.map (affineSubalgebraMap B)).left
        (affineFamilyBaseArrow t A) (affineFamilyBaseArrow t A)
        (Over.w ((Over.mk t).iteratedSliceBackward.map (affineSubalgebraMap B)))
        (Over.w ((Over.mk t).iteratedSliceBackward.map (affineSubalgebraMap B))) := rfl

/-- Restricting an arrow already defined on the fixed family base. -/
def affineFamilyBaseArrowMap (A : Type u) [CommRing A] [Algebra R A]
    (φ : L ⟶ M) : AffineFamilyArrow f t L M A :=
  ((relative f).map (affineFamilyBaseArrow t A).op.toLoc).toFunctor.map φ

private def identitySliceIso :
    (Over.mk t).iteratedSliceBackward.obj
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≅
        Over.mk (𝟙 (Over.mk t)) :=
  ((Over.mk t).iteratedSliceEquiv.unitIso.app (Over.mk (𝟙 (Over.mk t)))).symm

/-- Actual arrows are exactly the sections on the identity affine base. -/
def relativeIsomBaseEquiv :
    (L ⟶ M) ≃ (relativeIsomPresheaf f L M).obj
      (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :=
  (Pseudofunctor.presheafHomObjHomEquiv (relative f)).trans
    ((((relative f).presheafHom L M).mapIso (identitySliceIso t).op).toEquiv.trans
      Equiv.ulift.symm)

private lemma presheafHom_identity_restrict
    {C : Type*} [Category* C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {T U : C}
    {L M : F.obj (.mk (op T))} (a : U ⟶ T) (φ : L ⟶ M) :
    (F.presheafHom L M).map
      (Over.homMk a (by simp) : Over.mk a ⟶ Over.mk (𝟙 T)).op
      (F.presheafHomObjHomEquiv φ) =
        (F.map a.op.toLoc).toFunctor.map φ := by
  change pullHom (F := F) (F.presheafHomObjHomEquiv φ) a a a = _
  simp [Pseudofunctor.presheafHomObjHomEquiv, pullHom,
    Pseudofunctor.mapComp'_id_comp_hom_app,
    Pseudofunctor.mapComp'_id_comp_inv_app, ← Functor.map_comp,
    ← reassoc_of% Cat.Hom₂.comp_app, ← Cat.Hom₂.comp_app]

set_option maxHeartbeats 2000000 in
/-- Restriction of the identity section is ordinary pullback of the original
arrow, including the identity and composition coherence. -/
lemma relativeIsomBaseEquiv_restrict
    (A : Type u) [CommRing A] [Algebra R A] (φ : L ⟶ M) :
    ((relativeIsomPresheaf f L M).map (affineBaseProjection R A).op
      (relativeIsomBaseEquiv f t L M φ)).down =
        affineFamilyBaseArrowMap f t L M A φ := by
  let F := (relative f).presheafHom L M
  let a := affineFamilyBaseArrow t A
  have h :
      (Over.mk t).iteratedSliceBackward.map (affineBaseProjection R A) ≫
          (identitySliceIso t).hom =
        (Over.homMk a (by simp) : Over.mk a ⟶ Over.mk (𝟙 (Over.mk t))) := by
    apply Over.OverMorphism.ext
    apply Over.OverMorphism.ext
    simp [affineBaseProjection, identitySliceIso, a, affineFamilyBaseArrow,
      Over.iteratedSliceBackward]
  change F.map
      ((Over.mk t).iteratedSliceBackward.map (affineBaseProjection R A)).op
      (F.map (identitySliceIso t).hom.op
        ((relative f).presheafHomObjHomEquiv φ)) = _
  rw [← Functor.map_comp_apply, ← op_comp, h]
  exact presheafHom_identity_restrict (relative f) a φ

/-- Each specified actual arrow descends to a finite algebra stage. -/
theorem exists_affineFamilyArrow_subalgebra
    (h : HasAffineSubalgebraSectionDescent (relativeIsomPresheaf f L M))
    (A : Type u) [CommRing A] [Algebra R A]
    (φ : AffineFamilyArrow f t L M A) (s : Finset A) :
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      ∃ φ₀ : AffineFamilyArrow f t L M B,
        affineFamilyArrowRestrict f t L M B φ₀ = φ := by
  obtain ⟨B, hB, hs, φ₀, hφ₀⟩ := h A (ULift.up φ) s
  exact ⟨B, hB, hs, φ₀.down, congrArg ULift.down hφ₀⟩

/-- Equality of actual base arrows after extension is detected at a finite
algebra stage. -/
theorem exists_affineFamilyArrow_equality_subalgebra
    (h : HasAffineSubalgebraEqualityDescent (relativeIsomPresheaf f L M))
    (A : Type u) [CommRing A] [Algebra R A] (φ ψ : L ⟶ M)
    (hφψ : affineFamilyBaseArrowMap f t L M A φ =
      affineFamilyBaseArrowMap f t L M A ψ) (s : Finset A) :
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      affineFamilyBaseArrowMap f t L M B φ =
        affineFamilyBaseArrowMap f t L M B ψ := by
  have he :
      (relativeIsomPresheaf f L M).map (affineBaseProjection R A).op
          (relativeIsomBaseEquiv f t L M φ) =
        (relativeIsomPresheaf f L M).map (affineBaseProjection R A).op
          (relativeIsomBaseEquiv f t L M ψ) := by
    apply ULift.ext
    simpa only [relativeIsomBaseEquiv_restrict] using hφψ
  obtain ⟨B, hB, hs, hBφψ⟩ :=
    h A (relativeIsomBaseEquiv f t L M φ) (relativeIsomBaseEquiv f t L M ψ) he s
  refine ⟨B, hB, hs, ?_⟩
  simpa only [relativeIsomBaseEquiv_restrict] using congrArg ULift.down hBφψ

/-- Specified actual arrows descend, and equality of arrows defined on the
fixed base is detected, at finite algebra stages containing prescribed
coefficients. -/
def HasAffineFamilyArrowApproximation : Prop :=
  (∀ (A : Type u) [CommRing A] [Algebra R A]
    (φ : AffineFamilyArrow f t L M A) (s : Finset A),
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      ∃ φ₀ : AffineFamilyArrow f t L M B,
        affineFamilyArrowRestrict f t L M B φ₀ = φ) ∧
  (∀ (A : Type u) [CommRing A] [Algebra R A] (φ ψ : L ⟶ M)
    (_ : affineFamilyBaseArrowMap f t L M A φ =
      affineFamilyBaseArrowMap f t L M A ψ) (s : Finset A),
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      affineFamilyBaseArrowMap f t L M B φ =
        affineFamilyBaseArrowMap f t L M B ψ)

/-- The two presheaf descent properties give the actual-arrow formulation. -/
theorem hasAffineFamilyArrowApproximation_of_descent
    (hsection : HasAffineSubalgebraSectionDescent (relativeIsomPresheaf f L M))
    (hequality : HasAffineSubalgebraEqualityDescent (relativeIsomPresheaf f L M)) :
    HasAffineFamilyArrowApproximation f t L M :=
  ⟨exists_affineFamilyArrow_subalgebra f t L M hsection,
    exists_affineFamilyArrow_equality_subalgebra f t L M hequality⟩

/-- Focused Isom representability implies both actual-arrow approximation
properties. -/
theorem hasAffineFamilyArrowApproximation_of_isomRepresentability
    (h : ProperLineBundleIsomRepresentabilityStatement.{u})
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    HasAffineFamilyArrowApproximation f t L M :=
  hasAffineFamilyArrowApproximation_of_descent f t L M
    (affineIsomSectionDescent_of_isomRepresentability h f hf hflat hfp t L M)
    (affineIsomEqualityDescent_of_isomRepresentability h f hf hflat hfp t L M)

/-- Focused Hom representability implies both actual-arrow approximation
properties through the published Hom-to-Isom comparison. -/
theorem hasAffineFamilyArrowApproximation_of_homRepresentability
    (h : ProperLineBundleHomRepresentabilityStatement.{u})
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    HasAffineFamilyArrowApproximation f t L M :=
  hasAffineFamilyArrowApproximation_of_isomRepresentability f t L M
    (properLineBundleIsomRepresentability_of_hom h) hf hflat hfp

/-- For a proper flat locally finitely presented morphism, the published Hom
theorem discharges representability in actual-arrow approximation. -/
theorem hasAffineFamilyArrowApproximation
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    HasAffineFamilyArrowApproximation f t L M :=
  hasAffineFamilyArrowApproximation_of_homRepresentability f t L M
    properLineBundleHomRepresentability hf hflat hfp

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
