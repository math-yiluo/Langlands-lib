import Langlands.AlgebraicGeometry.Picard.PicardZeroSubfunctor

/-! # Universal geometric Picard-zero bundles -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- A Picard-zero family is universal when every Picard-zero class is uniquely its
actual rigidified pullback. No preservation or coherence theorem is assumed here. -/
def IsUniversalPicardZero {P : Over S} (L : RigidifiedFamily A P) : Prop :=
  IsPicardZeroFamily A L ∧
    ∀ (T : Over S) (q : PicardZeroClasses A T), ∃! h : T ⟶ P,
      RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
        (unitSection_comp A) L T h = q.val

/-- The universal property is equivalently unique classification of actual families. -/
lemma isUniversalPicardZero_iff {P : Over S} (L : RigidifiedFamily A P) :
    IsUniversalPicardZero A L ↔
      IsPicardZeroFamily A L ∧
        ∀ (T : Over S) (M : RigidifiedFamily A T), IsPicardZeroFamily A M →
          ∃! h : T ⟶ P, Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom
            (unitSection A) (unitSection_comp A) h).obj L ≅ M) := by
  constructor
  · intro hL
    refine ⟨hL.1, fun T M hM ↦ ?_⟩
    simpa only [RigidifiedLineBundle.classifyingMap_eq_iff] using
      hL.2 T ⟨RigidifiedLineBundle.classOf A.X.hom
        (unitSection A) (unitSection_comp A) M, hM⟩
  · rintro ⟨hL, h⟩
    refine ⟨hL, ?_⟩
    intro T ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h M =>
      change ∃! a, RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
        (unitSection_comp A) L T a =
          RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) M
      simpa only [RigidifiedLineBundle.classifyingMap_eq_iff] using h T M hq

variable (stability : PicardZeroPullbackStatement.{u})

/-- Classify by the actual pullback of a specified Picard-zero rigidified family. -/
def picardZeroClassifyingMap {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsPicardZeroFamily A L) (T : Over S) :
    (T ⟶ P) → PicardZeroClasses A T :=
  fun h ↦ picardZeroClassesPullback stability A h
    ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L, hL⟩

@[simp] lemma picardZeroClassifyingMap_val {P T : Over S}
    (L : RigidifiedFamily A P) (hL : IsPicardZeroFamily A L) (h : T ⟶ P) :
    (picardZeroClassifyingMap A stability L hL T h).val =
      RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
        (unitSection_comp A) L T h := rfl

/-- The universal property makes the restricted actual classification map bijective. -/
lemma picardZeroClassifyingMap_bijective {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZero A L) (T : Over S) :
    Function.Bijective (picardZeroClassifyingMap A stability L hL.1 T) := by
  apply (Function.bijective_iff_existsUnique _).mpr
  intro q
  obtain ⟨h, hh, hu⟩ := hL.2 T q
  exact ⟨h, Subtype.ext hh, fun k hk ↦ hu k (congrArg Subtype.val hk)⟩

/-- The classification equivalence is derived from the actual universal property. -/
def picardZeroClassifyingEquiv {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZero A L) (T : Over S) :
    (T ⟶ P) ≃ PicardZeroClasses A T :=
  Equiv.ofBijective _ (picardZeroClassifyingMap_bijective A stability L hL T)

variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})

include coherence in
lemma picardZeroClassifyingMap_comp {P T U : Over S} (L : RigidifiedFamily A P)
    (hL : IsPicardZeroFamily A L) (h : T ⟶ U) (k : U ⟶ P) :
    picardZeroClassifyingMap A stability L hL T (h ≫ k) =
      picardZeroClassesPullback stability A h
        (picardZeroClassifyingMap A stability L hL U k) := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classifyingMap_comp A.X.hom
    (unitSection A) (unitSection_comp A) coherence L h k

include coherence in
lemma picardZeroClassifyingMap_id {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsPicardZeroFamily A L) :
    picardZeroClassifyingMap A stability L hL P (𝟙 P) =
      ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L, hL⟩ := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classifyingMap_id A.X.hom
    (unitSection A) (unitSection_comp A) coherence L

/-- A universal Picard-zero family represents the actual Picard-zero presheaf. -/
def picardZeroRepresentableBy {P : Over S} (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZero A L) :
    (picardZeroPresheaf stability A coherence).RepresentableBy P where
  homEquiv := picardZeroClassifyingEquiv A stability L hL _
  homEquiv_comp h k := picardZeroClassifyingMap_comp A stability coherence L hL.1 h k

/-- The canonical parameter-scheme comparison induced by two universal families. -/
def picardZeroComparisonIso {P Q : Over S}
    (L : RigidifiedFamily A P) (M : RigidifiedFamily A Q)
    (hL : IsUniversalPicardZero A L) (hM : IsUniversalPicardZero A M) : P ≅ Q :=
  (picardZeroRepresentableBy A stability coherence L hL).uniqueUpToIso
    (picardZeroRepresentableBy A stability coherence M hM)

end Langlands.AbelianScheme
