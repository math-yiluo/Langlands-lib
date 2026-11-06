import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyBaseChangeProof

/-! # Translation invariance of actual pulled-back families at geometric points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Base change along the identity neither creates nor destroys translation invariance. -/
theorem isTranslationInvariant_fibreLineBundle_id_iff {S : Scheme.{u}}
    (A : AbelianScheme S) (F : LineBundle A.X.left) :
    GroupScheme.IsTranslationInvariant ((baseChange (𝟙 S)).obj A).toGrp
        (fibreLineBundle A F (𝟙 S)) ↔
      GroupScheme.IsTranslationInvariant A.toGrp F := by
  have h := GroupScheme.isTranslationInvariant_pullback_iso_iff
    (GroupScheme.baseChangeIdIso A.toGrp) F
  rw [GroupScheme.baseChangeIdIso_hom_left] at h
  exact h

/-- The actual family pulled back along `s` is translation invariant exactly when the
restriction of the original family to the fibre over `s` is. -/
theorem isTranslationInvariant_relativePullback_iff_fibre {S : Scheme.{u}}
    (A : AbelianScheme S) (T : Over S) {V : Scheme.{u}} (s : V ⟶ T.left)
    (L : RigidifiedFamily A T) :
    GroupScheme.IsTranslationInvariant ((baseChange (s ≫ T.hom)).obj A).toGrp
        (familyLineBundle (T := Over.mk (s ≫ T.hom)) A
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A)
            (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T)).obj L)) ↔
      GroupScheme.IsTranslationInvariant ((baseChange s).obj ((baseChange T.hom).obj A)).toGrp
        (fibreLineBundle ((baseChange T.hom).obj A) (familyLineBundle A L) s) := by
  have h₁ := GroupScheme.isTranslationInvariant_pullback_iso_iff
    (GroupScheme.baseChangeCompIso T.hom s A.toGrp).symm
    (familyLineBundle (T := Over.mk (s ≫ T.hom)) A
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T)).obj L))
  have h₂ := GroupScheme.isTranslationInvariant_iff_of_iso _
    (geometricPointPullbackLineBundleIso A T s L)
  exact h₁.symm.trans h₂

/-- At a geometric point, a Picard-zero pulled-back family has translation-invariant
fibre restriction of the original family. -/
theorem isTranslationInvariant_fibre_of_isPicardZeroFamily_relativePullback
    {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (L : RigidifiedFamily A T)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ T.left)
    (hL : IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T)).obj L)) :
    GroupScheme.IsTranslationInvariant ((baseChange s).obj ((baseChange T.hom).obj A)).toGrp
      (fibreLineBundle ((baseChange T.hom).obj A) (familyLineBundle A L) s) :=
  (isTranslationInvariant_relativePullback_iff_fibre A T s L).mp
    (isTranslationInvariant_of_isGeometricallyPicardZero K _ hL)

/-- A line bundle `M` on an abelian scheme `G` over `B` has an open subset of `B` that
detects translation invariance of its restrictions to the geometric fibres: a geometric
point `t` with algebraically closed residue field lands in it exactly when the restriction
of `M` to the fibre of `G` over `t` is translation invariant. -/
def HasOpenFibreTranslationInvarianceLocus {B : Scheme.{u}} (G : AbelianScheme B)
    (M : LineBundle G.X.left) : Prop :=
  ∃ W : B.Opens, ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ B),
    GroupScheme.IsTranslationInvariant ((baseChange t).obj G).toGrp
        (fibreLineBundle G M t) ↔
      Set.range t ⊆ (W : Set B)

/-- If every line bundle on every abelian scheme has an open set detecting translation
invariance of its geometric fibres, then the actual pulled-back families of a rigidified
family have an open set detecting their Picard-zero property at geometric points. -/
theorem exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion
    (hcrit : ∀ {B : Scheme.{u}} (G : AbelianScheme B) (M : LineBundle G.X.left),
      HasOpenFibreTranslationInvarianceLocus G M)
    {S : Scheme.{u}} (A : AbelianScheme S) (P : Over S) (L : RigidifiedFamily A P) :
    ∃ U : P.left.Opens, ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ P.left),
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A)
          (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) ↔
        Set.range s ⊆ (U : Set P.left) := by
  obtain ⟨U, hU⟩ := hcrit ((baseChange P.hom).obj A) (familyLineBundle A L)
  refine ⟨U, fun K _ _ s ↦ ⟨fun hL ↦ ?_, fun hs ↦ ?_⟩⟩
  · exact (hU K s).mp
      (isTranslationInvariant_fibre_of_isPicardZeroFamily_relativePullback A P L K s hL)
  · have hfib := (hU K s).mpr hs
    have hpt := (isTranslationInvariant_relativePullback_iff_fibre A P s L).mpr hfib
    obtain ⟨W, hW⟩ := hcrit ((baseChange (s ≫ P.hom)).obj A)
      (familyLineBundle (T := Over.mk (s ≫ P.hom)) A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A)
          (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L))
    have hid := (hW K (𝟙 _)).mp
      ((isTranslationInvariant_fibreLineBundle_id_iff _ _).mpr hpt)
    intro K' _ _ t
    refine (hW K' t).mpr ?_
    intro x _
    exact hid ⟨x, rfl⟩

end Langlands.AbelianScheme
