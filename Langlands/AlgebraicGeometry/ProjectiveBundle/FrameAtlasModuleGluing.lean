import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationPullback

/-! # Module isomorphisms from restriction on an intersection-closed frame atlas -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules.OpenCoverHomGluing

/-- Transport-compatible local morphisms on a covering family of open immersions
have unique global gluing. -/
private lemma existsUnique_hom_of_transport {X : Scheme.{u}} {I : Type u}
    {Y : I → Scheme.{u}} (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, x ∈ (j i).opensRange) (A B : X.Modules)
    (φ : ∀ i, (Scheme.Modules.pullback (j i)).obj A ⟶
      (Scheme.Modules.pullback (j i)).obj B)
    (hcompat : ∀ (U V : I) (P : X.Opens)
      (hU : P ≤ (j U).opensRange) (hV : P ≤ (j V).opensRange),
      transport (j U) (restrictHom (j U) (φ U)) P hU =
        transport (j V) (restrictHom (j V) (φ V)) P hV) :
    ∃! f : A ⟶ B, ∀ i, (Scheme.Modules.pullback (j i)).map f = φ i := by
  let D : OpenCoverHomGluing.LocalFamily (fun U => (j U).opensRange) A B :=
    { θ := fun U P hP =>
        OpenCoverHomGluing.transport (j U) (OpenCoverHomGluing.restrictHom (j U) (φ U)) P hP
      nat := fun U P Q hP hQP x => OpenCoverHomGluing.transport_map _ _ P Q hP hQP x
      smul := fun U P hP r x => OpenCoverHomGluing.transport_smul _ _ P hP r x
      compat := hcompat }
  have key : ∀ (U : I) (W : (Y U).Opens),
      (D.hom hcover).app (j U ''ᵁ W) =
        (OpenCoverHomGluing.restrictHom (j U) (φ U)).app W := by
    intro U W
    rw [D.hom_app hcover U _ ((j U).image_le_opensRange W)]
    exact OpenCoverHomGluing.transport_image _ _ W ((j U).image_le_opensRange W)
  refine ⟨D.hom hcover,
    fun U => OpenCoverHomGluing.pullback_map_eq_of_app _ _ _ (key U), ?_⟩
  intro g hg
  apply OpenCoverHomGluing.hom_ext_of_local hcover
  intro U P hP
  obtain ⟨W, rfl⟩ : ∃ W, P = j U ''ᵁ W :=
    ⟨j U ⁻¹ᵁ P, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hP]⟩
  rw [key, OpenCoverHomGluing.app_image_eq_of_pullback_map _ g _ (hg U)]


private lemma transport_eq_of_common_restriction
    {X U V W : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X)
    (r : W ⟶ U) (s : W ⟶ V) (k : W ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion r]
    [IsOpenImmersion s] [IsOpenImmersion k]
    (hr : r ≫ i = k) (hs : s ≫ j = k)
    (hrange : i.opensRange ⊓ j.opensRange ≤ k.opensRange)
    {A B : X.Modules}
    (φi : (Scheme.Modules.pullback i).obj A ⟶ (Scheme.Modules.pullback i).obj B)
    (φj : (Scheme.Modules.pullback j).obj A ⟶ (Scheme.Modules.pullback j).obj B)
    (φk : (Scheme.Modules.pullback k).obj A ⟶ (Scheme.Modules.pullback k).obj B)
    (hi : (Scheme.Modules.pullback r).map φi ≫ compHom r i k hr B =
      compHom r i k hr A ≫ φk)
    (hj : (Scheme.Modules.pullback s).map φj ≫ compHom s j k hs B =
      compHom s j k hs A ≫ φk)
    (P : X.Opens) (hU : P ≤ i.opensRange) (hV : P ≤ j.opensRange) :
    transport i (restrictHom i φi) P hU =
      transport j (restrictHom j φj) P hV := by
  have H := square_compatible_of_common_restriction i j r s k hr hs φi φj φk hi hj
  have hrange' : i.opensRange ⊓ j.opensRange ≤ (r ≫ i).opensRange := by
    simpa only [hr] using hrange
  exact transport_compat i j r s (hr.trans hs.symm) hrange' φi φj
    (conj_square j r s i (hr.trans hs.symm) φi φj H) P hU hV

end Langlands.Scheme.Modules.OpenCoverHomGluing

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ} (a : FrameAtlas M n)
variable (hInf : ∀ U V : a.opens, U.val ⊓ V.val ∈ a.opens)

include hInf

/-- A common chart provided by closure of the frame basis under intersections. -/
abbrev intersection (U V : a.opens) : a.opens :=
  ⟨U.val ⊓ V.val, hInf U V⟩

/-- The common chart has exactly the intersection of the two chart ranges. -/
lemma chart_intersection_opensRange (U V : a.opens) :
    (a.cocycle.chart (a.intersection hInf U V)).opensRange =
      (a.cocycle.chart U).opensRange ⊓ (a.cocycle.chart V).opensRange := by
  simp only [CoordinateCocycle.chart_opensRange, openCover,
    Scheme.Opens.opensRange_ι, intersection, Scheme.Hom.preimage_inf]

set_option maxHeartbeats 400000 in
/-- Module morphisms on actual atlas charts glue uniquely if they commute with
restriction to every smaller chart. -/
lemma existsUnique_hom_of_restriction (A B : a.bundle.Modules)
    (φ : ∀ U : a.opens,
      (Scheme.Modules.pullback (a.cocycle.chart U)).obj A ⟶
        (Scheme.Modules.pullback (a.cocycle.chart U)).obj B)
    (hφ : ∀ {U V : a.openCover.I₀} (h : U ⟶ V),
      (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).map (φ V) ≫
          compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
            (a.cocycle.transition_chart h) B =
        compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
          (a.cocycle.transition_chart h) A ≫ φ U) :
    ∃! f : A ⟶ B, ∀ U : a.opens,
      (Scheme.Modules.pullback (a.cocycle.chart U)).map f = φ U := by
  let j : ∀ U : a.opens, a.cocycle.chartFunctor.obj U ⟶ a.bundle :=
    a.cocycle.chart
  have hcover : ∀ x : a.bundle, ∃ U : a.opens, x ∈ (j U).opensRange := by
    intro x
    exact ⟨a.cocycle.openCover.idx x, a.cocycle.openCover.covers x⟩
  have hcompat : ∀ (U V : a.opens) (P : a.bundle.Opens)
      (hU : P ≤ (j U).opensRange) (hV : P ≤ (j V).opensRange),
      OpenCoverHomGluing.transport (j U) (OpenCoverHomGluing.restrictHom (j U) (φ U)) P hU =
        OpenCoverHomGluing.transport (j V) (OpenCoverHomGluing.restrictHom (j V) (φ V)) P hV := by
    intro U V P hU hV
    let W := a.intersection hInf U V
    let hWU : W ⟶ U := homOfLE (show W.val ≤ U.val from inf_le_left)
    let hWV : W ⟶ V := homOfLE (show W.val ≤ V.val from inf_le_right)
    let r := a.cocycle.chartFunctor.map hWU
    let s := a.cocycle.chartFunctor.map hWV
    let : IsOpenImmersion r := inferInstanceAs
      (IsOpenImmersion (a.cocycle.relativeGluingData.functor.map hWU))
    let : IsOpenImmersion s := inferInstanceAs
      (IsOpenImmersion (a.cocycle.relativeGluingData.functor.map hWV))
    have hr : r ≫ j U = j W := a.cocycle.transition_chart hWU
    have hs : s ≫ j V = j W := a.cocycle.transition_chart hWV
    exact OpenCoverHomGluing.transport_eq_of_common_restriction (j U) (j V) r s (j W)
      hr hs (a.chart_intersection_opensRange hInf U V).ge
      (φ U) (φ V) (φ W) (hφ hWU) (hφ hWV) P hU hV

  exact OpenCoverHomGluing.existsUnique_hom_of_transport j hcover A B φ hcompat

set_option maxHeartbeats 400000 in
/-- Compatible isomorphisms on the actual atlas charts glue uniquely. -/
lemma existsUnique_iso_of_restriction (A B : a.bundle.Modules)
    (e : ∀ U : a.opens,
      (Scheme.Modules.pullback (a.cocycle.chart U)).obj A ≅
        (Scheme.Modules.pullback (a.cocycle.chart U)).obj B)
    (he : ∀ {U V : a.openCover.I₀} (h : U ⟶ V),
      (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).map (e V).hom ≫
          compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
            (a.cocycle.transition_chart h) B =
        compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
          (a.cocycle.transition_chart h) A ≫ (e U).hom) :
    ∃! E : A ≅ B, ∀ U : a.opens,
      (Scheme.Modules.pullback (a.cocycle.chart U)).map E.hom = (e U).hom := by
  obtain ⟨f, hf, hfunique⟩ :=
    a.existsUnique_hom_of_restriction hInf A B (fun U => (e U).hom) he
  have hinv : ∀ {U V : a.openCover.I₀} (h : U ⟶ V),
      (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).map (e V).inv ≫
          compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
            (a.cocycle.transition_chart h) A =
        compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
          (a.cocycle.transition_chart h) B ≫ (e U).inv := by
    intro U V h
    apply (Iso.inv_comp_eq
      ((Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).mapIso (e V))).2
    simp only [Functor.mapIso_hom]
    rw [← Category.assoc, he h]
    simp
  obtain ⟨g, hg, _⟩ :=
    a.existsUnique_hom_of_restriction hInf B A (fun U => (e U).inv) hinv
  have inverse_id {C D : a.bundle.Modules} (f : C ⟶ D) (g : D ⟶ C)
      (h : ∀ U : a.opens,
        (Scheme.Modules.pullback (a.cocycle.chart U)).map f ≫
          (Scheme.Modules.pullback (a.cocycle.chart U)).map g = 𝟙 _) :
      f ≫ g = 𝟙 C := by
    obtain ⟨q, _, hq⟩ :=
      a.existsUnique_hom_of_restriction hInf C C (fun _ => 𝟙 _) (by intros; simp)
    apply (hq (f ≫ g) ?_).trans (hq (𝟙 C) ?_).symm
    · intro U
      simpa only [Functor.map_comp] using h U
    · intro U
      simp
  have hfg : f ≫ g = 𝟙 A := inverse_id f g (by
    intro U
    rw [hf U, hg U]
    exact (e U).hom_inv_id)
  have hgf : g ≫ f = 𝟙 B := inverse_id g f (by
    intro U
    rw [hg U, hf U]
    exact (e U).inv_hom_id)
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro E hE
  apply Iso.ext
  exact hfunique E.hom hE

/-- The isomorphism determined by restriction-compatible actual chart comparisons. -/
def restrictionIso (A B : a.bundle.Modules)
    (e : ∀ U : a.opens,
      (Scheme.Modules.pullback (a.cocycle.chart U)).obj A ≅
        (Scheme.Modules.pullback (a.cocycle.chart U)).obj B)
    (he : ∀ {U V : a.openCover.I₀} (h : U ⟶ V),
      (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).map (e V).hom ≫
          compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
            (a.cocycle.transition_chart h) B =
        compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
          (a.cocycle.transition_chart h) A ≫ (e U).hom) : A ≅ B :=
  (a.existsUnique_iso_of_restriction hInf A B e he).exists.choose

/-- The glued isomorphism has the prescribed forward map on every actual chart. -/
lemma restrictionIso_local (A B : a.bundle.Modules)
    (e : ∀ U : a.opens,
      (Scheme.Modules.pullback (a.cocycle.chart U)).obj A ≅
        (Scheme.Modules.pullback (a.cocycle.chart U)).obj B)
    (he : ∀ {U V : a.openCover.I₀} (h : U ⟶ V),
      (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).map (e V).hom ≫
          compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
            (a.cocycle.transition_chart h) B =
        compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
          (a.cocycle.transition_chart h) A ≫ (e U).hom)
    (U : a.opens) :
    (Scheme.Modules.pullback (a.cocycle.chart U)).map (a.restrictionIso hInf A B e he).hom =
      (e U).hom :=
  (a.existsUnique_iso_of_restriction hInf A B e he).exists.choose_spec U

end Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas
