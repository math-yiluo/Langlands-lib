import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Mathlib.AlgebraicGeometry.Restrict

/-! # Restriction of an actual universal rigidified family to an open Picard-zero locus -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}}

/-- The actual open subscheme, with its structure map to the original base. -/
def openLocusParameter (P : Over S) (U : P.left.Opens) : Over S :=
  Over.mk (U.ι ≫ P.hom)

/-- The canonical inclusion of the open parameter scheme over the base. -/
def openLocusInclusion (P : Over S) (U : P.left.Opens) :
    openLocusParameter P U ⟶ P :=
  Over.homMk U.ι rfl

instance (P : Over S) (U : P.left.Opens) : Mono (openLocusInclusion P U) := by
  let : Mono (openLocusInclusion P U).left := inferInstanceAs (Mono U.ι)
  exact Over.mono_of_mono_left _

/-- The image of the inclusion is precisely the specified open subset. -/
@[simp] lemma openLocusInclusion_range (P : Over S) (U : P.left.Opens) :
    Set.range (openLocusInclusion P U).left = (U : Set P.left) :=
  U.range_ι

/-- Factor a map whose image lies in the open subset through the actual open subscheme. -/
def openLocusLift (P : Over S) (U : P.left.Opens) {T : Over S}
    (h : T ⟶ P) (hh : Set.range h.left ⊆ (U : Set P.left)) :
    T ⟶ openLocusParameter P U := by
  let l : T.left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι h.left (by rwa [U.range_ι])
  exact Over.homMk l (by
    change l ≫ (U.ι ≫ P.hom) = T.hom
    dsimp [l]
    rw [IsOpenImmersion.lift_fac_assoc]
    exact h.w)

@[simp] lemma openLocusLift_fac (P : Over S) (U : P.left.Opens) {T : Over S}
    (h : T ⟶ P) (hh : Set.range h.left ⊆ (U : Set P.left)) :
    openLocusLift P U h hh ≫ openLocusInclusion P U = h := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (X := U.toScheme) U.ι h.left _

/-- Every map through the inclusion has image in the open subset. -/
lemma range_comp_openLocusInclusion (P : Over S) (U : P.left.Opens) {T : Over S}
    (h : T ⟶ openLocusParameter P U) :
    Set.range (h ≫ openLocusInclusion P U).left ⊆ (U : Set P.left) := by
  rintro _ ⟨x, rfl⟩
  exact (h.left x).property

/-- Image containment is exactly unique factorization in the category of schemes over the base. -/
lemma existsUnique_openLocusLift_iff (P : Over S) (U : P.left.Opens) {T : Over S}
    (h : T ⟶ P) :
    (∃! k : T ⟶ openLocusParameter P U, k ≫ openLocusInclusion P U = h) ↔
      Set.range h.left ⊆ (U : Set P.left) := by
  constructor
  · rintro ⟨k, hk, _⟩
    rw [← hk]
    exact range_comp_openLocusInclusion P U k
  · intro hh
    refine ⟨openLocusLift P U h hh, openLocusLift_fac P U h hh, ?_⟩
    intro k hk
    apply (cancel_mono (openLocusInclusion P U)).mp
    rw [hk, openLocusLift_fac]

variable (A : AbelianScheme S)

/-- An open locus for Picard-zero classes, tested by the actual pullback classifier on every
scheme over the base. This predicate makes no existence assertion. -/
def IsPicardZeroOpenLocus {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens) : Prop :=
  ∀ (T : Over S) (h : T ⟶ P),
    IsPicardZeroClass A (RigidifiedLineBundle.classifyingMap A.X.hom
      (unitSection A) (unitSection_comp A) L T h) ↔
        Set.range h.left ⊆ (U : Set P.left)

/-- Class membership of a classifier is the family predicate on the actual pulled-back bundle. -/
lemma isPicardZeroClass_classifyingMap_iff {P T : Over S}
    (L : RigidifiedFamily A P) (h : T ⟶ P) :
    IsPicardZeroClass A (RigidifiedLineBundle.classifyingMap A.X.hom
      (unitSection A) (unitSection_comp A) L T h) ↔
        IsPicardZeroFamily A ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) h).obj L) :=
  Iff.rfl

/-- The open-locus predicate equivalently tests every actual pulled-back family. -/
lemma isPicardZeroOpenLocus_iff {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens) :
    IsPicardZeroOpenLocus A L U ↔
      ∀ (T : Over S) (h : T ⟶ P),
        IsPicardZeroFamily A ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) h).obj L) ↔
            Set.range h.left ⊆ (U : Set P.left) :=
  Iff.rfl

/-- The specified family restricted by actual rigidified relative pullback along the inclusion. -/
def restrictedRigidifiedFamily {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens) : RigidifiedFamily A (openLocusParameter P U) :=
  (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
    (unitSection_comp A) (openLocusInclusion P U)).obj L

/-- Classification by the restricted family is classification by the original family after
composition with the open inclusion. Coherence is supplied by the published proof. -/
lemma restrictedRigidifiedFamily_classifyingMap {P T : Over S}
    (L : RigidifiedFamily A P) (U : P.left.Opens) (h : T ⟶ openLocusParameter P U) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (restrictedRigidifiedFamily A L U) T h =
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      L T (h ≫ openLocusInclusion P U) :=
  (RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A)
    (unitSection_comp A) RigidifiedModule.pullbackCoherence L h
    (openLocusInclusion P U)).symm

/-- The restricted family belongs to Picard zero whenever the specified open is its locus. -/
lemma restrictedRigidifiedFamily_picardZero {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens) (hU : IsPicardZeroOpenLocus A L U) :
    IsPicardZeroFamily A (restrictedRigidifiedFamily A L U) := by
  apply (isPicardZeroClass_classifyingMap_iff A L (openLocusInclusion P U)).mp
  apply (hU _ _).mpr
  rw [openLocusInclusion_range]

/-- Restricting an ambient universal family to its specified open Picard-zero locus gives
exactly the existing intrinsic universal property for Picard-zero classes. -/
lemma restrictedRigidifiedFamily_universal {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)
    (hU : IsPicardZeroOpenLocus A L U) :
    IsUniversalPicardZero A (restrictedRigidifiedFamily A L U) := by
  refine ⟨restrictedRigidifiedFamily_picardZero A L U hU, ?_⟩
  intro T q
  obtain ⟨h, hh, hu⟩ := (hL T).existsUnique q.val
  have hr : Set.range h.left ⊆ (U : Set P.left) := (hU T h).mp (by
    rw [hh]
    exact q.property)
  refine ⟨openLocusLift P U h hr, ?_, ?_⟩
  · change RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
      (unitSection_comp A) (restrictedRigidifiedFamily A L U) T
      (openLocusLift P U h hr) = q.val
    rw [restrictedRigidifiedFamily_classifyingMap, openLocusLift_fac]
    exact hh
  · intro k hk
    apply (cancel_mono (openLocusInclusion P U)).mp
    rw [openLocusLift_fac]
    apply hu
    rw [← restrictedRigidifiedFamily_classifyingMap]
    exact hk

/-- Conditional existence of a dual parameter scheme from an ambient universal family and
an actual open Picard-zero locus; neither input is asserted to exist here. -/
lemma hasDualScheme_of_isPicardZeroOpenLocus {P : Over S} (L : RigidifiedFamily A P)
    (U : P.left.Opens)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)
    (hU : IsPicardZeroOpenLocus A L U) : HasDualScheme A :=
  ⟨openLocusParameter P U, restrictedRigidifiedFamily A L U,
    restrictedRigidifiedFamily_universal A L U hL hU⟩

end Langlands.AbelianScheme
