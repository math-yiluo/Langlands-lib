import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidification
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Normalizing an actual bundle along both unit axes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.AbelianScheme Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S T : Scheme.{u}} (A : AbelianScheme S)

/-- Cancel the restriction to the first unit axis using the first projection. -/
def firstAxisNormalizedClass (c : IsoClasses preservation (mumfordProduct A).left) :
    IsoClasses preservation (mumfordProduct A).left :=
  c / (show IsoClasses preservation (mumfordProduct A).left from
    pullbackHom preservation (pullback.fst A.X.hom A.X.hom)
      (pullbackHom preservation (mumfordSection A) c))

/-- Cancel the second restriction after normalizing the first. -/
def twoAxisNormalizedClass (c : IsoClasses preservation (mumfordProduct A).left) :
    IsoClasses preservation (mumfordProduct A).left :=
  firstAxisNormalizedClass preservation A c /
    (show IsoClasses preservation (mumfordProduct A).left from
      pullbackHom preservation (pullback.snd A.X.hom A.X.hom)
        (pullbackHom preservation (twoAxisSecond A)
          (firstAxisNormalizedClass preservation A c)))

lemma firstAxisNormalizedClass_first
    (c : IsoClasses preservation (mumfordProduct A).left) :
    pullbackHom preservation (mumfordSection A)
      (firstAxisNormalizedClass preservation A c) = 1 := by
  erw [firstAxisNormalizedClass, map_div,
    pullbackHom_comp_eq preservation _ _
      (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X),
    pullbackHom_id]
  exact div_self' _

lemma firstAxisNormalizedClass_second_unit
    (c : IsoClasses preservation (mumfordProduct A).left) :
    pullbackHom preservation (unitSection A)
      (pullbackHom preservation (twoAxisSecond A)
        (firstAxisNormalizedClass preservation A c)) = 1 := by
  rw [pullbackHom_comp, ← twoAxis_unit_comp, ← pullbackHom_comp,
    firstAxisNormalizedClass_first, map_one]

lemma twoAxisNormalizedClass_first
    (c : IsoClasses preservation (mumfordProduct A).left) :
    pullbackHom preservation (mumfordSection A)
      (twoAxisNormalizedClass preservation A c) = 1 := by
  have hi : mumfordSection A ≫ pullback.snd A.X.hom A.X.hom =
      A.X.hom ≫ unitSection A :=
    relativeSection_snd A.X.hom (unitSection A) (unitSection_comp A) A.X
  erw [twoAxisNormalizedClass, map_div, firstAxisNormalizedClass_first,
    pullbackHom_comp_eq preservation _ _ hi,
    ← pullbackHom_comp preservation A.X.hom (unitSection A)
      (pullbackHom preservation (twoAxisSecond A)
        (firstAxisNormalizedClass preservation A c)),
    firstAxisNormalizedClass_second_unit preservation A c,
    (pullbackHom preservation A.X.hom).map_one]
  exact div_one _

lemma twoAxisNormalizedClass_second
    (c : IsoClasses preservation (mumfordProduct A).left) :
    pullbackHom preservation (twoAxisSecond A)
      (twoAxisNormalizedClass preservation A c) = 1 := by
  have hj : twoAxisSecond A ≫ pullback.snd A.X.hom A.X.hom = 𝟙 A.X.left := by
    exact pullback.lift_snd _ _ _
  erw [twoAxisNormalizedClass, map_div,
    pullbackHom_comp_eq preservation _ _ hj, pullbackHom_id]
  exact div_self' _

lemma twoAxisNormalizedClass_eq_self
    (c : IsoClasses preservation (mumfordProduct A).left)
    (hi : pullbackHom preservation (mumfordSection A) c = 1)
    (hj : pullbackHom preservation (twoAxisSecond A) c = 1) :
    twoAxisNormalizedClass preservation A c = c := by
  simp only [twoAxisNormalizedClass, firstAxisNormalizedClass, hi, map_one,
    div_one, hj]

private lemma pullbackHom_square
    {U V W Z : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ Z) (c : U ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) (q : IsoClasses preservation Z) :
    pullbackHom preservation a (pullbackHom preservation b q) =
      pullbackHom preservation c (pullbackHom preservation d q) := by
  rw [pullbackHom_comp, h, ← pullbackHom_comp]

variable (B : AbelianScheme T)
  (q : (mumfordProduct B).left ⟶ (mumfordProduct A).left)
  (f : B.X.left ⟶ A.X.left)
  (hfst : q ≫ pullback.fst A.X.hom A.X.hom =
    pullback.fst B.X.hom B.X.hom ≫ f)
  (hsnd : q ≫ pullback.snd A.X.hom A.X.hom =
    pullback.snd B.X.hom B.X.hom ≫ f)
  (hi : mumfordSection B ≫ q = f ≫ mumfordSection A)
  (hj : twoAxisSecond B ≫ q = f ≫ twoAxisSecond A)

include hfst hi in
lemma pullback_firstAxisNormalizedClass
    (c : IsoClasses preservation (mumfordProduct A).left) :
    pullbackHom preservation q (firstAxisNormalizedClass preservation A c) =
      firstAxisNormalizedClass preservation B (pullbackHom preservation q c) := by
  dsimp only [firstAxisNormalizedClass]
  erw [map_div, pullbackHom_square preservation _ _ _ _ hfst,
    ← pullbackHom_square preservation _ _ _ _ hi]
  rfl

include hfst hsnd hi hj in
/-- Normalization commutes with maps preserving both projections and axes. -/
lemma pullback_twoAxisNormalizedClass
    (c : IsoClasses preservation (mumfordProduct A).left) :
    pullbackHom preservation q (twoAxisNormalizedClass preservation A c) =
      twoAxisNormalizedClass preservation B (pullbackHom preservation q c) := by
  dsimp only [twoAxisNormalizedClass]
  erw [map_div, pullbackHom_square preservation _ _ _ _ hsnd,
    ← pullbackHom_square preservation _ _ _ _ hj,
    pullback_firstAxisNormalizedClass preservation A B q f hfst hi]
  rfl

/-- Choose an actual bundle representing the normalized class. -/
def twoAxisNormalizedBundle (E : LineBundle (mumfordProduct A).left) :
    LineBundle (mumfordProduct A).left :=
  Quotient.out (twoAxisNormalizedClass preservation A (isoClass preservation E))

lemma isoClass_twoAxisNormalizedBundle (E : LineBundle (mumfordProduct A).left) :
    isoClass preservation (twoAxisNormalizedBundle preservation A E) =
      twoAxisNormalizedClass preservation A (isoClass preservation E) :=
  Quotient.out_eq _

/-- The chosen actual normalized bundle has an actual first-axis trivialization. -/
def twoAxisNormalizedBundleFirst (E : LineBundle (mumfordProduct A).left) :
    (Scheme.Modules.pullback (mumfordSection A)).obj
      (twoAxisNormalizedBundle preservation A E).obj ≅ structureSheaf A.X.left := by
  have h : isoClass preservation ((pullback (mumfordSection A)).obj
      (twoAxisNormalizedBundle preservation A E)) =
      isoClass preservation (trivial A.X.left) := by
    change pullbackHom preservation (mumfordSection A)
      (isoClass preservation (twoAxisNormalizedBundle preservation A E)) = 1
    rw [isoClass_twoAxisNormalizedBundle, twoAxisNormalizedClass_first]
  exact (forget A.X.left).mapIso (Classical.choice (isoClass_eq_iff.mp h))

/-- The chosen actual normalized bundle has an actual second-axis trivialization. -/
def twoAxisNormalizedBundleSecond (E : LineBundle (mumfordProduct A).left) :
    (Scheme.Modules.pullback (twoAxisSecond A)).obj
      (twoAxisNormalizedBundle preservation A E).obj ≅ structureSheaf A.X.left := by
  have h : isoClass preservation ((pullback (twoAxisSecond A)).obj
      (twoAxisNormalizedBundle preservation A E)) =
      isoClass preservation (trivial A.X.left) := by
    change pullbackHom preservation (twoAxisSecond A)
      (isoClass preservation (twoAxisNormalizedBundle preservation A E)) = 1
    rw [isoClass_twoAxisNormalizedBundle, twoAxisNormalizedClass_second]
  exact (forget A.X.left).mapIso (Classical.choice (isoClass_eq_iff.mp h))

/-- The same actual bundle carries compatible two-axis trivializations. -/
def twoAxisNormalizedBundleRigidification (E : LineBundle (mumfordProduct A).left) :
    TwoAxisRigidification (unitSection A) (unitSection A)
      (mumfordSection A) (twoAxisSecond A) (twoAxis_unit_comp A)
      (twoAxisNormalizedBundle preservation A E).obj :=
  twoAxisRigidificationOfTrivializations A (twoAxisNormalizedBundle preservation A E)
    (twoAxisNormalizedBundleFirst preservation A E)
    (twoAxisNormalizedBundleSecond preservation A E)

include hfst hsnd hi hj in
/-- Normalizing an existing extension preserves its restriction if both
restrictions of the target bundle to its axes are trivial. -/
def twoAxisNormalizedBundleRestrictionIso
    (E : LineBundle (mumfordProduct A).left)
    (D : LineBundle (mumfordProduct B).left)
    (e : ((pullback q).obj E).obj ≅ D.obj)
    (α : (Scheme.Modules.pullback (mumfordSection B)).obj D.obj ≅
      structureSheaf B.X.left)
    (β : (Scheme.Modules.pullback (twoAxisSecond B)).obj D.obj ≅
      structureSheaf B.X.left) :
    ((pullback q).obj (twoAxisNormalizedBundle preservation A E)).obj ≅ D.obj := by
  have he : pullbackHom preservation q (isoClass preservation E) =
      isoClass preservation D :=
    isoClass_eq_of_iso (ObjectProperty.isoMk _ e)
  have hα : pullbackHom preservation (mumfordSection B) (isoClass preservation D) = 1 :=
    isoClass_eq_of_iso (ObjectProperty.isoMk _ α)
  have hβ : pullbackHom preservation (twoAxisSecond B) (isoClass preservation D) = 1 :=
    isoClass_eq_of_iso (ObjectProperty.isoMk _ β)
  have hn : isoClass preservation
      ((pullback q).obj (twoAxisNormalizedBundle preservation A E)) =
      isoClass preservation D := by
    change pullbackHom preservation q
      (isoClass preservation (twoAxisNormalizedBundle preservation A E)) =
        isoClass preservation D
    rw [isoClass_twoAxisNormalizedBundle,
      pullback_twoAxisNormalizedClass preservation A B q f hfst hsnd hi hj,
      he, twoAxisNormalizedClass_eq_self preservation B _ hα hβ]
  exact (forget (mumfordProduct B).left).mapIso
    (Classical.choice (isoClass_eq_iff.mp hn))

end Langlands.AlgebraicGeometry.Picard.LineBundle
