import Langlands.AlgebraicGeometry.SchemeFilteredPropertyModelStatement
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.FinitePresentation

/-! # Construction of smooth and flat filtered-ring models -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

private theorem propertyModelExistence
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hdesc : ∀ {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀]
      {A : Type u} [CommRing A] [Algebra A₀ A]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))
      [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f],
      P (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))) →
      ∃ (T : Subalgebra A₀ A), T.FG ∧
        P (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))) :
    SchemeFilteredPropertyModelExistence P := by
  intro J _ _ F c hc X g _ _ _ hg
  let : Algebra (ULift.{u} ℤ) c.pt := ULift.algebra' ℤ c.pt
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T₀, hT₀, _, X₀, f₀, π₀, hfp₀, hqc₀, hqs₀, hpb₀⟩ :=
    NoetherianApproximation.schemeSubalgebraDescent
      (A₀ := ULift.{u} ℤ) g ∅
  let : LocallyOfFinitePresentation f₀ := hfp₀
  let : QuasiCompact f₀ := hqc₀
  let : QuasiSeparated f₀ := hqs₀
  let : Algebra.FiniteType (ULift.{u} ℤ) T₀ := T₀.fg_iff_finiteType.mp hT₀
  let : IsNoetherianRing T₀ := Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) T₀
  have hg₀ : P (pullback.snd f₀
      (Spec.map (CommRingCat.ofHom (algebraMap T₀ c.pt)))) := by
    rw [← hpb₀.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp P _ _ hg
  obtain ⟨T₁, hT₁, hg₁⟩ := hdesc f₀ hg₀
  let : Algebra.FiniteType T₀ T₁ := T₁.fg_iff_finiteType.mp hT₁
  let : Algebra.FiniteType (ULift.{u} ℤ) T₁ := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType (ULift.{u} ℤ) T₀)
    (inferInstance : Algebra.FiniteType T₀ T₁)
  let : Algebra.FinitePresentation (ULift.{u} ℤ) T₁ :=
    (Algebra.FinitePresentation.of_finiteType (R := ULift.{u} ℤ) (A := T₁)).mp
      inferInstance
  let b : Spec (CommRingCat.of T₁) ⟶ Spec (CommRingCat.of T₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap T₀ T₁))
  let a₁ : Spec c.pt ⟶ Spec (CommRingCat.of T₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap T₁ c.pt))
  have ha₁ : a₁ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap T₀ c.pt)) := by
    dsimp [a₁, b]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let g₁ := pullback.snd f₀ b
  let : LocallyOfFinitePresentation g₁ := inferInstance
  let : QuasiCompact g₁ := inferInstance
  let : QuasiSeparated g₁ := inferInstance
  have houter₁ : IsPullback π₀ g f₀ (a₁ ≫ b) := ha₁.symm ▸ hpb₀
  have hright₁ : IsPullback (pullback.fst f₀ b) g₁ f₀ b :=
    IsPullback.of_hasPullback f₀ b
  let π₁ : X ⟶ pullback f₀ b :=
    hright₁.lift π₀ (g ≫ a₁) (by simpa only [Category.assoc] using houter₁.w)
  have hpb₁ : IsPullback π₁ g g₁ a₁ := houter₁.of_right' hright₁
  let z : Spec (CommRingCat.of T₁) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) T₁))
  let : LocallyOfFinitePresentation z := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  let D : Jᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let d : Cone D := Scheme.Spec.mapCone c.op
  let hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc.op
  let t : D ⟶ (Functor.const Jᵒᵖ).obj (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    { app := fun i => Spec.map (CommRingCat.isInitial.to (F.obj i.unop))
      naturality := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  let (i : Jᵒᵖ) : IsAffine (D.obj i) := by
    dsimp [D]
    infer_instance
  have ha : d.π ≫ t = (Functor.const Jᵒᵖ).map (a₁ ≫ z) := by
    ext i
    exact specULiftZIsTerminal.hom_ext _ _
  obtain ⟨i, q, hq, _⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t z d hd a₁ ha
  let Xj := pullback g₁ q
  let gj : Xj ⟶ Spec (F.obj i.unop) := pullback.snd g₁ q
  have houter : IsPullback π₁ g g₁ (Spec.map (c.ι.app i.unop) ≫ q) := by
    simpa only [D, d] using hq ▸ hpb₁
  have hright : IsPullback (pullback.fst g₁ q) gj g₁ q :=
    IsPullback.of_hasPullback g₁ q
  exact ⟨i.unop, Xj, gj, _, inferInstance, inferInstance, inferInstance,
    MorphismProperty.pullback_snd _ _ hg₁, houter.of_right' hright⟩

/-- Smoothness descends first over noetherian integer subalgebras, then
through an actual original ring stage. -/
theorem schemeFilteredSmoothModelExistence :
    SchemeFilteredSmoothModelExistence.{u} := by
  apply propertyModelExistence @Smooth
  intro A₀ _ _ A _ _ X f _ _ _ h
  let : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))) := h
  obtain ⟨T, hT, _, hs⟩ :=
    NoetherianApproximation.smoothSubalgebraDescent (A := A) f ∅
  exact ⟨T, hT, hs⟩

/-- Flatness descends by the corresponding published subalgebra theorem. -/
theorem schemeFilteredFlatModelExistence :
    SchemeFilteredFlatModelExistence.{u} := by
  apply propertyModelExistence @Flat
  intro A₀ _ _ A _ _ X f _ _ _ h
  let : Flat (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))) := h
  obtain ⟨T, hT, _, hs⟩ :=
    Flat.exists_fg_subalgebra_of_flat_pullback_snd (A := A) f ∅
  exact ⟨T, hT, hs⟩

/-- Both structural properties admit finitely presented models. -/
theorem schemeFilteredSmoothFlatModelExistence :
    SchemeFilteredSmoothFlatModelExistence.{u} :=
  ⟨schemeFilteredSmoothModelExistence, schemeFilteredFlatModelExistence⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
