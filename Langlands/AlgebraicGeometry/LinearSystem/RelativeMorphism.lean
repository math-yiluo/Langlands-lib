import Langlands.AlgebraicGeometry.LinearSystem.Morphism
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.TwistOne

/-! # Relative linear-system morphisms and pullback of generating sections -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false

variable {X Y T : Scheme.{u}} {L : LineBundle X} {n : ℕ}
  {s : Fin (n + 1) → GlobalSections L.obj}

/-- The whole inverse image of a coordinate chart is the generation open of its section. -/
lemma linearSystemMap_preimage {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) (i : Fin (n + 1)) :
    linearSystemMap p hs ⁻¹ᵁ projectiveSpaceCoordinateOpen K n i =
      trivializationOpen L.obj (s i) := by
  ext x
  constructor
  · intro hx
    have hy : (X.fromSpecResidueField x ≫ linearSystemMap p hs)
        (IsLocalRing.closedPoint (X.residueField x)) ∈
          projectiveSpaceCoordinateOpen K n i := by simpa [Scheme.fromSpecResidueField_apply] using hx
    have he : X.fromSpecResidueField x
        (IsLocalRing.closedPoint (X.residueField x)) = x :=
      Scheme.fromSpecResidueField_apply x _
    exact he ▸ mem_trivializationOpen_of_comp_mem p hs (X.fromSpecResidueField x) i hy
  · intro hx
    have hy : ∀ t, X.fromSpecResidueField x t ∈ trivializationOpen L.obj (s i) := by
      intro t
      simpa [Scheme.fromSpecResidueField_apply] using hx
    simpa [Scheme.fromSpecResidueField_apply] using comp_mem_coordinateOpen p hs hy (IsLocalRing.closedPoint (X.residueField x))

/-- Pulling back generating sections gives generating sections on every source scheme. -/
lemma pullbackSections_generate (f : Y ⟶ X)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    ∀ y : Y, ∃ i, y ∈ nonvanishingLocus ((LineBundle.pullback f).obj L).obj
      (pullbackSection f L.obj (s i)) := by
  intro y
  obtain ⟨i, hi⟩ := exists_mem_trivializationOpen hs (f y)
  refine ⟨i, ?_⟩
  rw [lineBundleResidueOpenComparison]
  change y ∈ trivializationOpen ((Scheme.Modules.pullback f).obj L.obj)
    (pullbackSection f L.obj (s i))
  rw [lineBundlePullbackSectionOpen]
  exact hi

/-- Membership in the generation open of a pulled-back line-bundle section. -/
lemma mem_pullback_trivializationOpen_iff (f : Y ⟶ X) (σ : GlobalSections L.obj) (y : Y) :
    y ∈ trivializationOpen ((LineBundle.pullback f).obj L).obj
        (pullbackSection f L.obj σ) ↔ f y ∈ trivializationOpen L.obj σ := by
  change y ∈ trivializationOpen ((Scheme.Modules.pullback f).obj L.obj)
    (pullbackSection f L.obj σ) ↔ _
  rw [lineBundlePullbackSectionOpen]
  rfl

/-- A ratio of pulled-back sections is the original ratio along the composite. -/
lemma sectionRatio_pullback (f : Y ⟶ X) (h : T ⟶ Y)
    (σ s₀ : GlobalSections L.obj)
    (hh : ∀ t, h t ∈ trivializationOpen ((LineBundle.pullback f).obj L).obj
      (pullbackSection f L.obj s₀)) :
    sectionRatio ((LineBundle.pullback f).obj L) h
        (pullbackSection f L.obj σ) (pullbackSection f L.obj s₀) =
      sectionRatio L (h ≫ f) σ s₀ := by
  have hh' : ∀ t, (h ≫ f) t ∈ trivializationOpen L.obj s₀ := by
    intro t
    exact (mem_pullback_trivializationOpen_iff f s₀ (h t)).mp (hh t)
  apply (sectionRatio_eq_iff hh _ _).mpr
  have : IsIso (((Scheme.Modules.pullbackComp h f).hom.app L.obj).app ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance ⊤
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp h f).hom.app L.obj).app ⊤)).injective
  change (((Scheme.Modules.pullbackComp h f).hom.app L.obj).app ⊤)
      (sectionRatio L (h ≫ f) σ s₀ •
        pullbackSection h ((Scheme.Modules.pullback f).obj L.obj)
          (pullbackSection f L.obj s₀)) =
    (((Scheme.Modules.pullbackComp h f).hom.app L.obj).app ⊤)
      (pullbackSection h ((Scheme.Modules.pullback f).obj L.obj)
        (pullbackSection f L.obj σ))
  rw [Scheme.Modules.Hom.app_smul, pullbackSection_comp, pullbackSection_comp]
  exact sectionRatio_smul hh' σ

/-- Point maps of pulled-back sections are point maps of the original sections. -/
lemma pointMap_pullback {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (h : T ⟶ Y)
    (j : Fin (n + 1))
    (hh : ∀ t, h t ∈ trivializationOpen ((LineBundle.pullback f).obj L).obj
      (pullbackSection f L.obj (s j))) :
    pointMap (L := (LineBundle.pullback f).obj L) (f ≫ p)
        (fun i ↦ pullbackSection f L.obj (s i)) h j hh =
      pointMap p s (h ≫ f) j (fun t ↦ by
        exact (mem_pullback_trivializationOpen_iff f (s j) (h t)).mp (hh t)) := by
  unfold pointMap
  apply chartMap_ringHom_congr
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [chartRingHom_C, Category.assoc]
  · intro i
    simp only [chartRingHom_X]
    exact sectionRatio_pullback f h (s i) (s j) hh

/-- The glued linear-system morphism commutes with arbitrary pullback of its sections. -/
lemma linearSystemMap_pullback {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    linearSystemMap (f ≫ p) (pullbackSections_generate f hs) =
      f ≫ linearSystemMap p hs := by
  apply Scheme.hom_ext_of_forall
  intro y
  obtain ⟨j, hj⟩ := exists_mem_trivializationOpen (pullbackSections_generate f hs) y
  refine ⟨trivializationOpen ((LineBundle.pullback f).obj L).obj
    (pullbackSection f L.obj (s j)), hj, ?_⟩
  let U := trivializationOpen ((LineBundle.pullback f).obj L).obj
    (pullbackSection f L.obj (s j))
  calc
    U.ι ≫ linearSystemMap (f ≫ p) (pullbackSections_generate f hs) =
        pointMap (L := (LineBundle.pullback f).obj L) (f ≫ p)
          (fun i ↦ pullbackSection f L.obj (s i)) U.ι j (ι_mem U) :=
      comp_linearSystemMap (L := (LineBundle.pullback f).obj L)
        (f ≫ p) (pullbackSections_generate f hs) U.ι j (ι_mem U)
    _ = pointMap p s (U.ι ≫ f) j (fun t ↦
        (mem_pullback_trivializationOpen_iff f (s j) (U.ι t)).mp (ι_mem U t)) :=
      pointMap_pullback p f U.ι j (ι_mem U)
    _ = U.ι ≫ f ≫ linearSystemMap p hs := by
      rw [← Category.assoc]
      exact (comp_linearSystemMap p hs _ j (fun t ↦
        (mem_pullback_trivializationOpen_iff f (s j) (U.ι t)).mp (ι_mem U t))).symm

/-- The integral linear-system map, available over every scheme. -/
def integralLinearSystemMap
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    X ⟶ ProjectiveSpace (ULift.{u} ℤ) n :=
  linearSystemMap (specULiftZIsTerminal.from X) hs

/-- The integral map commutes with arbitrary pullback of its sections. -/
lemma integralLinearSystemMap_pullback (f : Y ⟶ X)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    integralLinearSystemMap (pullbackSections_generate f hs) =
      f ≫ integralLinearSystemMap hs := by
  unfold integralLinearSystemMap
  rw [← linearSystemMap_pullback]
  congr 1
  exact specULiftZIsTerminal.hom_ext _ _

/-- The actual relative projective-space morphism defined by generating sections. -/
def relativeLinearSystemMap {S : Scheme.{u}} (p : X ⟶ S)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    X ⟶ RelativeProjectiveSpace S n :=
  RelativeProjectiveSpace.lift n p (integralLinearSystemMap hs)

@[reassoc (attr := simp)]
lemma relativeLinearSystemMap_toBase {S : Scheme.{u}} (p : X ⟶ S)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    relativeLinearSystemMap p hs ≫ RelativeProjectiveSpace.toBase S n = p :=
  RelativeProjectiveSpace.lift_toBase _ _ _

@[reassoc (attr := simp)]
lemma relativeLinearSystemMap_toIntegral {S : Scheme.{u}} (p : X ⟶ S)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    relativeLinearSystemMap p hs ≫ RelativeProjectiveSpace.toIntegral S n =
      integralLinearSystemMap hs :=
  RelativeProjectiveSpace.lift_toIntegral _ _ _

/-- Relative coordinate charts have exactly the expected whole inverse images. -/
lemma relativeLinearSystemMap_preimage {S : Scheme.{u}} (p : X ⟶ S)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) (i : Fin (n + 1)) :
    relativeLinearSystemMap p hs ⁻¹ᵁ RelativeProjectiveSpace.coordinateOpen S n i =
      trivializationOpen L.obj (s i) := by
  rw [RelativeProjectiveSpace.coordinateOpen, ← Scheme.Hom.comp_preimage,
    relativeLinearSystemMap_toIntegral]
  exact linearSystemMap_preimage _ hs i

/-- Pulling back the sections commutes with the relative map, including a change of base. -/
lemma relativeLinearSystemMap_pullback {S S' : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S') (f : Y ⟶ X) (g : S' ⟶ S)
    (w : f ≫ p = q ≫ g)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    relativeLinearSystemMap q (pullbackSections_generate f hs) ≫
        RelativeProjectiveSpace.map n g =
      f ≫ relativeLinearSystemMap p hs := by
  apply RelativeProjectiveSpace.hom_ext
  · simpa using w.symm
  · simp only [Category.assoc, RelativeProjectiveSpace.map_toIntegral,
      relativeLinearSystemMap_toIntegral]
    exact integralLinearSystemMap_pullback f hs

end Langlands.AlgebraicGeometry.LinearSystem
