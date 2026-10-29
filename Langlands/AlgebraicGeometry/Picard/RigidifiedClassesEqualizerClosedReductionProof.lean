import Langlands.AlgebraicGeometry.Picard.MumfordParameterAxes
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedReductionStatement
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeEquivalence
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality
import Langlands.AlgebraicGeometry.ClosedLocusFromAffineChartsProof

/-! # Proof of the reduction of the closed agreement locus to an affine base -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry

namespace RigidifiedClassesEqualizerClosedReduction

set_option quotPrecheck false in
/-- Actual rigidified pullback of classes for the abelian scheme `A`. -/
local notation "cp[" A "]" =>
  RigidifiedLineBundle.classesPullback (A).X.hom (unitSection A)
    (unitSection_comp A)

variable {S : Scheme.{u}}

/-- Agreement of two classes after pullback is stable under precomposition. -/
lemma agree_of_fac (A : AbelianScheme S) {T' T'' U : Over S} {h : T' ⟶ U} (a : T' ⟶ T'')
    (k : T'' ⟶ U) (fac : a ≫ k = h) {q r : RigidifiedClasses A U}
    (hk : cp[A] k q = cp[A] k r) : cp[A] h q = cp[A] h r := by
  rw [← fac, ← classesPullback_comp, ← classesPullback_comp, hk]

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

/-- The map on classes induced by actual ground-base change of rigidified families. -/
def classesBaseChange (T : Over S') :
    RigidifiedClasses A ((Over.map b).obj T) → RigidifiedClasses ((baseChange b).obj A) T :=
  Quotient.map (familyBaseChange b A T).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(familyBaseChange b A T).mapIso e⟩)

lemma classesBaseChange_pullback {T U : Over S'} (h : T ⟶ U)
    (x : RigidifiedClasses A ((Over.map b).obj U)) :
    classesBaseChange b A T (cp[A] ((Over.map b).map h) x) =
      cp[(baseChange b).obj A] h (classesBaseChange b A U x) := by
  refine Quotient.inductionOn x (fun F ↦ ?_)
  exact Quotient.sound ⟨(familyBaseChangeNaturality b A h).app F⟩

lemma classesBaseChange_injective (T : Over S') :
    Function.Injective (classesBaseChange b A T) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | h F => ?_
  induction y using Quotient.inductionOn with | h G => ?_
  obtain ⟨e⟩ := Quotient.exact hxy
  exact Quotient.sound ⟨(familyBaseChangeEquivalence b A T).fullyFaithfulFunctor.preimageIso e⟩

end BaseChange

variable {A : AbelianScheme S} {T : Over S} (q r : RigidifiedClasses A T)

/-- The two classes agree after pullback along `g`, viewed as a morphism over `S`. -/
def Agree ⦃Y : Scheme.{u}⦄ (g : Y ⟶ T.left) : Prop :=
  cp[A] (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T) q =
    cp[A] (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T) r

lemma agree_iff {T' : Over S} (h : T' ⟶ T) : cp[A] h q = cp[A] h r ↔ Agree q r h.left := by
  constructor
  · exact agree_of_fac A (Over.homMk (𝟙 T'.left) (by simp) :
      Over.mk (h.left ≫ T.hom) ⟶ T') h (by ext; simp)
  · exact agree_of_fac A (Over.homMk (𝟙 T'.left) (by simp) :
      T' ⟶ Over.mk (h.left ≫ T.hom)) (Over.homMk h.left) (by ext; simp)

lemma agree_comp ⦃Y Y' : Scheme.{u}⦄ (f : Y' ⟶ Y) (g : Y ⟶ T.left) (hg : Agree q r g) :
    Agree q r (f ≫ g) :=
  agree_of_fac A (Over.homMk f (by simp) : Over.mk ((f ≫ g) ≫ T.hom) ⟶ Over.mk (g ≫ T.hom))
    (Over.homMk g) (by ext; simp) hg

lemma agree_of_affineOpens (zariski : RigidifiedClassesZariskiSeparatedStatement.{u})
    ⦃Y : Scheme.{u}⦄ (g : Y ⟶ T.left)
    (hg : ∀ V : T.left.affineOpens, Agree q r ((g ⁻¹ᵁ (V : T.left.Opens)).ι ≫ g)) :
    Agree q r g := by
  let 𝒰 : Y.OpenCover := Y.openCoverOfIsOpenCover
    (fun V : T.left.affineOpens ↦ g ⁻¹ᵁ (V : T.left.Opens))
    (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top T.left))
  refine zariski S A (Over.mk (g ≫ T.hom)) 𝒰 _ _ fun V ↦ ?_
  rw [classesPullback_comp, classesPullback_comp]
  exact (agree_iff q r _).2 (hg V)

lemma chart (affine : RigidifiedClassesEqualizerClosedAffineStatement.{u})
    (U : T.left.affineOpens) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ (U : T.left.Opens).toScheme), IsClosedImmersion ι ∧
      ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ (U : T.left.Opens).toScheme),
        (∃ k : Y ⟶ Z, k ≫ ι = g) ↔ Agree q r (g ≫ (U : T.left.Opens).ι) := by
  have hU := U.2
  let b : Spec Γ(T.left, (U : T.left.Opens)) ⟶ S := hU.fromSpec ≫ T.hom
  let φ : (Over.map b).obj (Over.mk (𝟙 _)) ⟶ T := Over.homMk hU.fromSpec (by simp [b])
  obtain ⟨Z, ι, hι, hZ⟩ := affine _ ((baseChange b).obj A)
    (classesBaseChange b A _ (cp[A] φ q)) (classesBaseChange b A _ (cp[A] φ r))
  refine ⟨Z, ι ≫ hU.isoSpec.inv, inferInstance, fun Y g ↦ ?_⟩
  have key := hZ (Over.mk (g ≫ hU.isoSpec.hom)) (Over.homMk (g ≫ hU.isoSpec.hom) (by simp))
  rw [← classesBaseChange_pullback, ← classesBaseChange_pullback,
    (classesBaseChange_injective b A _).eq_iff, classesPullback_comp, classesPullback_comp,
    agree_iff] at key
  have hleft : ((Over.map b).map (Over.homMk (g ≫ hU.isoSpec.hom) (by simp) :
      Over.mk (g ≫ hU.isoSpec.hom) ⟶ Over.mk (𝟙 _)) ≫ φ).left = g ≫ (U : T.left.Opens).ι := by
    simp [φ, hU.isoSpec_hom_fromSpec]
  rw [hleft] at key
  rw [← key]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [← hk]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← Category.assoc, hk]
    simp

end RigidifiedClassesEqualizerClosedReduction

open RigidifiedClassesEqualizerClosedReduction in
/-- The affine-base agreement locus and Zariski separatedness imply the general statement. -/
theorem rigidifiedClassesEqualizerClosedReduction :
    RigidifiedClassesEqualizerClosedReductionStatement.{u} := by
  intro affine zariski S A T q r
  obtain ⟨Z, ι, hι, hZ⟩ := closedLocusFromAffineCharts T.left (Agree q r) (agree_comp q r)
    (agree_of_affineOpens q r zariski) (chart q r affine)
  exact ⟨Z, ι, hι, fun T' h ↦ (hZ h.left).trans (agree_iff q r h).symm⟩

end Langlands.AbelianScheme
