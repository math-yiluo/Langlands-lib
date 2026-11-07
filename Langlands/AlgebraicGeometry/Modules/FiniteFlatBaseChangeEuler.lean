import Langlands.AlgebraicGeometry.Modules.FiniteSupportTwistEuler
import Langlands.AlgebraicGeometry.Modules.FiniteFlatPushforwardFreeCharts
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicProof
import Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Euler characteristics after a finite flat base change of the parameter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

variable {Y Y₁ Z Z₁ : Scheme.{u}}

/-- For an affine morphism `φ` and a line bundle `F`, `φ_* φ^* F ≅ F ⊗ φ_* 𝒪`. -/
def pushforwardPullbackLineBundleIso (φ : Z₁ ⟶ Z) (F : LineBundle Z) :
    (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj F.obj) ≅
      tensorObj F.obj ((Scheme.Modules.pushforward φ).obj (structureSheaf Z₁)) :=
  (Scheme.Modules.pushforward φ).mapIso (tensorRightUnitor _).symm ≪≫
    (lineBundleProjectionIso φ F (structureSheaf Z₁)).symm

/-- **Finite flat base change of the parameter multiplies the Euler characteristic by the
degree.** Let `q : Z ⟶ Y` and `s : Y ⟶ Spec K`, let `f : Y₁ ⟶ Y` be finite, flat and locally
of finite presentation with `f.finrank y = d` at every point, and let `φ : Z₁ ⟶ Z` be the base
change of `f` along `q`. Let `F` be a line bundle on `Z` with finite cohomology whose higher
direct images along `q` all have finite closed support. Then `φ^* F` has finite cohomology and
`χ(Z₁, φ^* F) = d · χ(Z, F)`. -/
theorem eulerCharacteristic_finiteFlatBaseChange
    {K : Type u} [Field K] (s : Y ⟶ Spec (CommRingCat.of K))
    (q : Z ⟶ Y) (f : Y₁ ⟶ Y) (φ : Z₁ ⟶ Z) (q₁ : Z₁ ⟶ Y₁) (hsq : IsPullback φ q₁ q f)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (d : ℕ)
    (hd : ∀ y : Y, f.finrank y = d)
    (F : LineBundle Z) (hsupp : ∀ n, HasFiniteClosedSupport ((higherDirectImage q n).obj F.obj))
    (hF : HasFiniteCohomology (q ≫ s) F.obj) :
    HasFiniteCohomology (φ ≫ q ≫ s) ((Scheme.Modules.pullback φ).obj F.obj) ∧
      ∀ hφ : HasFiniteCohomology (φ ≫ q ≫ s) ((Scheme.Modules.pullback φ).obj F.obj),
        eulerCharacteristic (φ ≫ q ≫ s) ((Scheme.Modules.pullback φ).obj F.obj) hφ =
          (d : ℤ) * eulerCharacteristic (q ≫ s) F.obj hF := by
  have hφfin : IsFinite φ := MorphismProperty.of_isPullback hsq.flip ‹IsFinite f›
  have : IsAffineHom φ := inferInstance
  let W := (Scheme.Modules.pushforward f).obj (structureSheaf Y₁)
  let e : (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj F.obj) ≅
      tensorObj F.obj ((Scheme.Modules.pullback q).obj W) :=
    pushforwardPullbackLineBundleIso φ F ≪≫
      tensorMapIso (Iso.refl _) (pushforwardStructureSheafBaseChangeIso f d hd q φ q₁ hsq)
  obtain ⟨hT, hχ⟩ := eulerCharacteristic_twist q F W d s
    (exists_freeChart_pushforward_structureSheaf f d hd) hsupp hF
  have hP : HasFiniteCohomology (q ≫ s)
      ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj F.obj)) :=
    hasFiniteCohomology_of_iso (q ≫ s) e.symm hT
  have hA := affinePushforwardEulerCharacteristic K Z₁ Z φ this (q ≫ s)
    ((Scheme.Modules.pullback φ).obj F.obj) ((LineBundle.pullback φ).obj F).isQuasicoherent
  refine ⟨hA.1.mpr hP, fun hφ => ?_⟩
  rw [hA.2 hφ hP, eulerCharacteristic_eq_of_iso (q ≫ s) hP hT e, hχ hT]

/-- Anchor proposition of this module (internal): over a field `K`, if all higher direct images
of a line bundle `F` along `q : Z ⟶ Y` have finite closed support and `F` has finite cohomology,
then (1) twisting `F` by the pullback of a module with free charts of rank `d` multiplies the
Euler characteristic by `d`, and (2) pulling `F` back along the base change of a finite flat
morphism of finite presentation and constant degree `d` multiplies it by `d`. -/
def FiniteSupportEulerScalingStatement : Prop :=
  (∀ (K : Type u) [Field K] (Y Z : Scheme.{u}) (s : Y ⟶ Spec (CommRingCat.of K)) (q : Z ⟶ Y)
    (F : LineBundle Z) (W : Y.Modules) (d : ℕ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj W ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d)))) →
    (∀ n, HasFiniteClosedSupport ((higherDirectImage q n).obj F.obj)) →
    ∀ hF : HasFiniteCohomology (q ≫ s) F.obj,
      HasFiniteCohomology (q ≫ s) (tensorObj F.obj ((Scheme.Modules.pullback q).obj W)) ∧
        ∀ hT : HasFiniteCohomology (q ≫ s)
            (tensorObj F.obj ((Scheme.Modules.pullback q).obj W)),
          eulerCharacteristic (q ≫ s) (tensorObj F.obj ((Scheme.Modules.pullback q).obj W)) hT =
            (d : ℤ) * eulerCharacteristic (q ≫ s) F.obj hF) ∧
  (∀ (K : Type u) [Field K] (Y Y₁ Z Z₁ : Scheme.{u}) (s : Y ⟶ Spec (CommRingCat.of K))
    (q : Z ⟶ Y) (f : Y₁ ⟶ Y) (φ : Z₁ ⟶ Z) (q₁ : Z₁ ⟶ Y₁), IsPullback φ q₁ q f →
    IsFinite f → Flat f → LocallyOfFinitePresentation f →
    ∀ d : ℕ, (∀ y : Y, f.finrank y = d) →
    ∀ F : LineBundle Z, (∀ n, HasFiniteClosedSupport ((higherDirectImage q n).obj F.obj)) →
    ∀ hF : HasFiniteCohomology (q ≫ s) F.obj,
      HasFiniteCohomology (φ ≫ q ≫ s) ((Scheme.Modules.pullback φ).obj F.obj) ∧
        ∀ hφ : HasFiniteCohomology (φ ≫ q ≫ s) ((Scheme.Modules.pullback φ).obj F.obj),
          eulerCharacteristic (φ ≫ q ≫ s) ((Scheme.Modules.pullback φ).obj F.obj) hφ =
            (d : ℤ) * eulerCharacteristic (q ≫ s) F.obj hF)

/-- The anchor proposition holds. -/
theorem finiteSupportEulerScaling : FiniteSupportEulerScalingStatement.{u} := by
  refine ⟨fun K _ Y Z s q F W d hW hsupp hF => eulerCharacteristic_twist q F W d s hW hsupp hF,
    fun K _ Y Y₁ Z Z₁ s q f φ q₁ hsq _ _ _ d hd F hsupp hF => ?_⟩
  exact eulerCharacteristic_finiteFlatBaseChange s q f φ q₁ hsq d hd F hsupp hF

end Langlands.AlgebraicGeometry.Modules.DerivedSections
