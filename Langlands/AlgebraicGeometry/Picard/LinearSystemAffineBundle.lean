import Langlands.AlgebraicGeometry.Picard.LinearSystemAffineExistence
import Langlands.AlgebraicGeometry.Picard.PushforwardLineBundle

/-! # The line bundle `N` on the Grassmannian with `O(W) ≅ L ⊗ N`

The class `[O(W)] - [L]` on `Y ×_R Gr` is trivial over the preimages of the admissible affine
opens of `Gr`: there `W` is the zero locus of a regular section of `L`. Since the projection
`Y ×_R Gr ⟶ Gr` is proper, flat and geometrically integral, it satisfies `p_* O = O`, and the
class is pulled back from a line bundle `N` on `Gr`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open scoped TensorProduct
open Scheme.TwoAffineOpenCover SectionZeroIdeal
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)
open PicardHilbertPiecesReduction (mapX mapX_comp mapX_congr dcl dcl_congr pb_comp_apply
  pb_iso_inv_hom)

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
  [IsProper π] [Flat π] [GeometricallyIntegral π] {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  (D : Rep R C.Q 1) {W : (pullback π D.p).IdealSheafData}
  (hW : ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
      (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k),
      W.comap (ptMap π D.p k hk) = LinSys.FOf L D k hk hP)

omit [IsNoetherianRing R] [IsProper π] [Flat π] [GeometricallyIntegral π] in
lemma classOf_pbLB {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : LineBundle Z) :
    (pbLB f M).classOf = Group.pullback f M.classOf :=
  (Group.pullback_lineBundle_classOf f M).symm

omit [IsNoetherianRing R] [IsProper π] [Flat π] [GeometricallyIntegral π] in
lemma dcl_zeroIdeal {Y : Scheme.{u}} (M : LineBundle Y) {σ : Γ(M.obj, ⊤)}
    (hreg : IsRegularSection M σ) (h : IsEffectiveCartierIdeal (zeroIdeal M σ)) :
    dcl (zeroIdeal M σ) h = M.classOf :=
  (LineBundle.classOf_eq_iff _ _).2 (nonempty_lineBundle_zeroIdeal_iso hreg)

omit [IsNoetherianRing R] in
include he hW in
/-- The class `[O(W)] - [L]` is trivial along a chart point. -/
lemma pullback_ptMap_class_eq_zero
    (hWrel : IsRelativeEffectiveCartierIdeal (pullback.snd π D.p) W)
    {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing B] (k : Spec (.of B) ⟶ D.Gr)
    [IsOpenImmersion k] (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k) :
    Group.pullback (ptMap π D.p k hk)
      (dcl W hWrel.1 - Group.pullback (pullback.fst π D.p) L.classOf) = 0 := by
  obtain ⟨h1, hd1⟩ := PicardHilbertPiecesReduction.flat_comap (ptMap π D.p k hk)
    (pullback.snd π D.p) W hWrel
  have hWO : W.comap (ptMap π D.p k hk) =
      zeroIdeal (pbLB (pullback.fst π (specMap R B)) L)
        (C.homEquivSections B (LinSys.vOf D k hk hP)) := hW k hk hP
  have hreg := (homEquivSections_regular_and_relativeEffective e he C _
    (LinSys.span_range_vOf D k hk hP)).1
  have hdz : dcl (W.comap (ptMap π D.p k hk)) h1.1 =
      Group.pullback (pullback.fst π (specMap R B)) L.classOf := by
    rw [dcl_congr hWO h1.1 (isEffectiveCartierIdeal_zeroIdeal hreg), dcl_zeroIdeal _ hreg,
      classOf_pbLB]
  have hfst : Group.pullback (ptMap π D.p k hk)
      (Group.pullback (pullback.fst π D.p) L.classOf) =
      Group.pullback (pullback.fst π (specMap R B)) L.classOf :=
    PicardHilbertPiecesReduction.pb_mapX_fst π k hk L.classOf
  rw [map_sub, ← hd1, hdz, hfst, sub_self]

set_option maxHeartbeats 1000000 in
include he hW in
/-- **The class of the universal divisor is `[L] + [N]` for a line bundle `N` on the
Grassmannian.** -/
theorem exists_lineBundle_universal
    (hWrel : IsRelativeEffectiveCartierIdeal (pullback.snd π D.p) W) :
    ∃ N : LineBundle D.Gr, dcl W hWrel.1 =
      Group.pullback (pullback.fst π D.p) L.classOf +
        Group.pullback (pullback.snd π D.p) N.classOf := by
  have : IsProper D.p := D.isProper_p
  have : IsLocallyNoetherian D.Gr := LocallyOfFiniteType.isLocallyNoetherian D.p
  have : GeometricallyConnected (pullback.snd π D.p) :=
    Langlands.AbelianScheme.TranslationOfSmoothFamily.geometricallyConnected_of_geometricallyIntegral _
  have hq : ∀ U : D.Gr.Opens, Function.Bijective ((pullback.snd π D.p).app U) := fun U =>
    bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected _ U
  let x := dcl W hWrel.1 - Group.pullback (pullback.fst π D.p) L.classOf
  have hx : ∀ t : D.Gr, ∃ U : D.Gr.Opens, t ∈ U ∧
      Group.pullback ((pullback.snd π D.p) ⁻¹ᵁ U).ι x = 0 := by
    intro t
    let P := LinSys.pointIdeals e he D
    obtain ⟨O, htO, hPO⟩ := P.cover t
    let O' : P.Adm := ⟨O, hPO⟩
    refine ⟨O.1, htO, ?_⟩
    let _ := affAlg D.p O
    have : IsNoetherianRing Γ(D.Gr, O.1) := IsLocallyNoetherian.component_noetherian O
    -- the class is trivial along the piece over `O`
    have hpiece : Group.pullback (P.pieceι O') x = 0 :=
      pullback_ptMap_class_eq_zero e he C D hW hWrel (affPt O) (affPt_comp D.p O) hPO
    -- transport to the open subscheme `q⁻¹ O`
    have hr : Set.range (P.pieceι O') =
        Set.range (Scheme.Opens.ι ((pullback.snd π D.p) ⁻¹ᵁ O.1)) := by
      rw [P.range_pieceι, Scheme.Opens.range_ι]
      rfl
    let iso := IsOpenImmersion.isoOfRangeEq (P.pieceι O')
      (Scheme.Opens.ι ((pullback.snd π D.p) ⁻¹ᵁ O.1)) hr
    have hfac : iso.hom ≫ Scheme.Opens.ι ((pullback.snd π D.p) ⁻¹ᵁ O.1) = P.pieceι O' :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have h2 : Group.pullback iso.hom
        (Group.pullback (Scheme.Opens.ι ((pullback.snd π D.p) ⁻¹ᵁ O.1)) x) = 0 := by
      rw [← pb_comp_apply, hfac, hpiece]
    rw [← pb_iso_inv_hom iso (Group.pullback _ x), h2, map_zero]
  obtain ⟨N, hN⟩ := PushforwardLineBundle.exists_classOf_pullback (pullback.snd π D.p) hq x hx
  refine ⟨N, ?_⟩
  rw [hN, add_sub_cancel]

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
