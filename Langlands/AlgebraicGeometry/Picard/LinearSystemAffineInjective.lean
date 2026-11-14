import Langlands.AlgebraicGeometry.Picard.LinearSystemAffinePoints
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Langlands.AlgebraicGeometry.GeometricallyIntegralConnected

/-! # Points of the Grassmannian are determined by their pullbacks of the universal divisor

Two points of the Grassmannian of rank-one quotients of `Q` over a locally noetherian test scheme
that pull back the universal divisor to the same ideal sheaf are equal. On affine pieces in
charts, the two zero loci are zero loci of regular sections `σ_{v₁}, σ_{v₂}` differing by a unit
of `Γ(Y_B, O) = B`; hence `v₂` is a unit multiple of `v₁` and both points are the same line
quotient. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open scoped TensorProduct
open Scheme.TwoAffineOpenCover SectionZeroIdeal
open Langlands.RingTheory.Grassmannian.LineQuotientCoordinates
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)

section Linear

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {M : X.Modules}
  {𝒰 : X.OrderedAffineCover} (C : CechRep π M 𝒰) {B : Type u} [CommRing B] [Algebra R B]

/-- **The section attached to `v` is `B`-linear in `v`.** -/
lemma homEquivSections_smul (b : B) (v : C.Q →ₗ[R] B) :
    C.homEquivSections B (b • v) =
      (algebraOfHom (pullback.snd π (specMap R B)) ⊤).algebraMap b • C.homEquivSections B v := by
  have h1 : C.kerEquivH0 B (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ B (b • v)) =
      b • C.kerEquivH0 B (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ B v) := by
    apply Subtype.ext
    change C.Θ B (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ B (b • v)).1 =
      b • C.Θ B (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ B v).1
    rw [Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv_smul, map_smul]
  change (CechRep.sectionsEquivH0 (π := π) (M := M) (𝒰 := 𝒰) B).symm
    (C.kerEquivH0 B (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ B (b • v))) = _
  rw [h1]
  let _ := moduleSectionsOfHom (pullback.snd π (specMap R B))
    ((Scheme.Modules.pullback (pullback.fst π (specMap R B))).obj M) ⊤
  exact (CechRep.sectionsEquivH0 (π := π) (M := M) (𝒰 := 𝒰) B).symm.map_smul b _

end Linear

section Units

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
  [IsProper π] [Flat π] [GeometricallyIntegral π] (B : Type u) [CommRing B] [Algebra R B]

/-- **`Γ(Y_B, O) = B`** for a proper flat geometrically integral `Y` over a noetherian ring. -/
lemma bijective_algebraMap_top :
    Function.Bijective (algebraOfHom (pullback.snd π (specMap R B)) ⊤).algebraMap := by
  have : GeometricallyConnected (pullback.snd π (specMap R B)) :=
    Langlands.AbelianScheme.TranslationOfSmoothFamily.geometricallyConnected_of_geometricallyIntegral _
  have h := bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
    (pullback.snd π (specMap R B)) ⊤
  have e : (pullback.snd π (specMap R B)).appLE ⊤ ⊤ le_top =
      (pullback.snd π (specMap R B)).app ⊤ := Scheme.Hom.appLE_eq_app _
  change Function.Bijective (((Scheme.ΓSpecIso (.of B)).inv ≫
    (pullback.snd π (specMap R B)).appLE ⊤ ⊤ le_top).hom)
  rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
  exact h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).inv)

/-- Units of `Γ(Y_B, O)` come from units of `B`. -/
lemma exists_isUnit_algebraMap_eq (c : Γ(pullback π (specMap R B), ⊤)) (hc : IsUnit c) :
    ∃ b : B, IsUnit b ∧ (algebraOfHom (pullback.snd π (specMap R B)) ⊤).algebraMap b = c := by
  let f : B ≃+* Γ(pullback π (specMap R B), ⊤) :=
    RingEquiv.ofBijective (algebraOfHom (pullback.snd π (specMap R B)) ⊤).algebraMap
      (bijective_algebraMap_top π B)
  exact ⟨f.symm c, hc.map f.symm, f.apply_symm_apply c⟩

end Units

section Injective

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
  [IsProper π] [Flat π] [GeometricallyIntegral π] {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  (D : Rep R C.Q 1)

omit [IsNoetherianRing R] [IsProper π] [Flat π] [GeometricallyIntegral π] in
lemma linePt_congr {B : Type u} [CommRing B] [Algebra R B] {v v' : C.Q →ₗ[R] B} (h : v = v')
    (hv : Ideal.span (Set.range v) = ⊤) (hv' : Ideal.span (Set.range v') = ⊤) :
    linePt v hv = linePt v' hv' := by
  subst h
  rfl

omit [IsNoetherianRing R] [IsProper π] [Flat π] [GeometricallyIntegral π] in
lemma ptOf_eq_linePt {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
    (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k) :
    LinSys.ptOf D k hk = linePt (LinSys.vOf D k hk hP) (LinSys.span_range_vOf D k hk hP) :=
  eq_linePt_coord _ _ _ _

include he in
/-- **Injectivity on chart points.** -/
theorem eq_of_comap_eq_of_inSomeChart {W : (pullback π D.p).IdealSheafData}
    (hW : ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
      (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k),
      W.comap (ptMap π D.p k hk) = LinSys.FOf L D k hk hP)
    {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing B]
    (k₁ k₂ : Spec (.of B) ⟶ D.Gr) (hk₁ : k₁ ≫ D.p = specMap R B)
    (hk₂ : k₂ ≫ D.p = specMap R B) (hP₁ : LinSys.InSomeChart D k₁)
    (hP₂ : LinSys.InSomeChart D k₂)
    (h : W.comap (ptMap π D.p k₁ hk₁) = W.comap (ptMap π D.p k₂ hk₂)) : k₁ = k₂ := by
  rw [hW k₁ hk₁ hP₁, hW k₂ hk₂ hP₂] at h
  have hreg := (homEquivSections_regular_and_relativeEffective e he C _
    (LinSys.span_range_vOf D k₁ hk₁ hP₁)).1
  obtain ⟨c, hc, hcσ⟩ := exists_isUnit_eq_smul_of_zeroIdeal_eq hreg h.symm
  obtain ⟨b, hb, rfl⟩ := exists_isUnit_algebraMap_eq π B c hc
  rw [← homEquivSections_smul] at hcσ
  have hv := (C.homEquivSections B).injective hcσ
  have hpt : LinSys.ptOf D k₁ hk₁ = LinSys.ptOf D k₂ hk₂ := by
    rw [ptOf_eq_linePt C D k₁ hk₁ hP₁, ptOf_eq_linePt C D k₂ hk₂ hP₂,
      linePt_congr C hv _ (by rw [← hv]; exact LinSys.span_range_vOf D k₂ hk₂ hP₂),
      linePt_smul _ (LinSys.span_range_vOf D k₁ hk₁ hP₁) b hb]
  calc k₁ = (D.pt B (LinSys.ptOf D k₁ hk₁)).1 := (LinSys.pt_ptOf D k₁ hk₁).symm
    _ = (D.pt B (LinSys.ptOf D k₂ hk₂)).1 := by rw [hpt]
    _ = k₂ := LinSys.pt_ptOf D k₂ hk₂

include he in
/-- **Points of the Grassmannian over a locally noetherian test are determined by the pullback of
the universal divisor.** -/
theorem eq_of_comap_mapX_eq {W : (pullback π D.p).IdealSheafData}
    (hW : ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
      (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k),
      W.comap (ptMap π D.p k hk) = LinSys.FOf L D k hk hP)
    {T' : Scheme.{u}} [IsLocallyNoetherian T'] {t' : T' ⟶ Spec (.of R)}
    (k₁ k₂ : T' ⟶ D.Gr) (hk₁ : k₁ ≫ D.p = t') (hk₂ : k₂ ≫ D.p = t')
    (h : W.comap (PicardHilbertPiecesReduction.mapX π k₁ hk₁) =
      W.comap (PicardHilbertPiecesReduction.mapX π k₂ hk₂)) : k₁ = k₂ := by
  refine Scheme.hom_ext_of_forall k₁ k₂ fun z => ?_
  obtain ⟨x₁, hx₁⟩ := TopologicalSpace.Opens.mem_iSup.mp (D.hV.ge (Set.mem_univ (k₁ z)))
  obtain ⟨x₂, hx₂⟩ := TopologicalSpace.Opens.mem_iSup.mp (D.hV.ge (Set.mem_univ (k₂ z)))
  have hxe₁ : x₁ = fun _ => x₁ 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have hxe₂ : x₂ = fun _ => x₂ 0 := funext fun i => by rw [Subsingleton.elim i 0]
  let O₀ : T'.Opens := k₁ ⁻¹ᵁ D.V x₁ ⊓ k₂ ⁻¹ᵁ D.V x₂
  obtain ⟨_, ⟨O, hO, rfl⟩, hzO, hOO₀⟩ :=
    T'.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ O₀ from ⟨hx₁, hx₂⟩) O₀.2
  refine ⟨O, hzO, ?_⟩
  let O' : T'.affineOpens := ⟨O, hO⟩
  let _ := affAlg t' O'
  have : IsNoetherianRing Γ(T', O) := IsLocallyNoetherian.component_noetherian O'
  have hc₁ : (affPt O' ≫ k₁) ≫ D.p = specMap R Γ(T', O) := by
    rw [Category.assoc, hk₁, affPt_comp]
  have hc₂ : (affPt O' ≫ k₂) ≫ D.p = specMap R Γ(T', O) := by
    rw [Category.assoc, hk₂, affPt_comp]
  have hP₁ : LinSys.InSomeChart D (affPt O' ≫ k₁) := by
    refine ⟨x₁ 0, ?_⟩
    rintro _ ⟨w, rfl⟩
    have hw : (affPt O') w ∈ O := (range_affPt O').subset ⟨w, rfl⟩
    rw [← hxe₁]
    exact (hOO₀ hw).1
  have hP₂ : LinSys.InSomeChart D (affPt O' ≫ k₂) := by
    refine ⟨x₂ 0, ?_⟩
    rintro _ ⟨w, rfl⟩
    have hw : (affPt O') w ∈ O := (range_affPt O').subset ⟨w, rfl⟩
    rw [← hxe₂]
    exact (hOO₀ hw).2
  have hcomap : W.comap (ptMap π D.p (affPt O' ≫ k₁) hc₁) =
      W.comap (ptMap π D.p (affPt O' ≫ k₂) hc₂) := by
    have e₁ : ptMap π D.p (affPt O' ≫ k₁) hc₁ =
        PicardHilbertPiecesReduction.mapX π (affPt O') (affPt_comp t' O') ≫
          PicardHilbertPiecesReduction.mapX π k₁ hk₁ :=
      (PicardHilbertPiecesReduction.mapX_comp π k₁ hk₁ (affPt O') (affPt_comp t' O')).symm
    have e₂ : ptMap π D.p (affPt O' ≫ k₂) hc₂ =
        PicardHilbertPiecesReduction.mapX π (affPt O') (affPt_comp t' O') ≫
          PicardHilbertPiecesReduction.mapX π k₂ hk₂ :=
      (PicardHilbertPiecesReduction.mapX_comp π k₂ hk₂ (affPt O') (affPt_comp t' O')).symm
    rw [e₁, e₂, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h]
  have key := eq_of_comap_eq_of_inSomeChart e he C D hW _ _ hc₁ hc₂ hP₁ hP₂ hcomap
  have hiso : affPt O' = hO.isoSpec.inv ≫ Scheme.Opens.ι O := (IsAffineOpen.isoSpec_inv_ι hO).symm
  rw [hiso, Category.assoc, Category.assoc] at key
  exact (cancel_epi _).1 key

end Injective

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
