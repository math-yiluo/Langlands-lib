import Langlands.AlgebraicGeometry.Picard.LinearSystemAffineInjective
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionSetup

/-! # Every divisor of the linear system is a pullback of the universal divisor

Let `E` be a relative effective Cartier divisor on `Y_{T'}` over a locally noetherian test `T'`
with `[O(E)] = [L_{T'}] + [N']` for a class `N'` on `T'`. On an affine open `Spec B ⊆ T'` where
`N'` is trivial, `O(E) ≅ L_B`, so the canonical section of `O(E)` becomes a section `σ` of `L_B`
with zero locus `E`; writing `σ = σ_v` with `v : Q → B`, the values of `v` generate the unit ideal
and the point of the Grassmannian given by the line quotient `v` pulls the universal divisor
back to `E`. These local points glue by injectivity. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open scoped TensorProduct
open Scheme.TwoAffineOpenCover SectionZeroIdeal
open Langlands.RingTheory.Grassmannian.LineQuotientCoordinates
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)
open PicardHilbertPiecesReduction (mapX mapX_comp mapX_congr dcl pb_comp_apply)

section Classes

/-- **Picard classes are trivial on small affine opens.** -/
lemma exists_affine_pullback_eq_zero {T : Scheme.{u}} (x : Group T) (z : T) :
    ∃ O : T.affineOpens, z ∈ O.1 ∧ Group.pullback (affPt O) x = 0 := by
  let N := Group.lineBundleRepresentative T x
  obtain ⟨O, hzO, t, ht⟩ := exists_affine_frame N z
  obtain ⟨eO⟩ := ht.nonempty_pullback_iso_unit O.1 le_rfl le_rfl
  refine ⟨O, hzO, ?_⟩
  have h0 : Group.pullback (Scheme.Opens.ι O.1) x = 0 := by
    rw [← Group.classOf_lineBundleRepresentative T x, Group.pullback_lineBundle_classOf,
      ← LineBundle.classOf_trivial, LineBundle.classOf_eq_iff]
    exact ⟨eO⟩
  have hiso : affPt O = O.2.isoSpec.inv ≫ Scheme.Opens.ι O.1 :=
    (IsAffineOpen.isoSpec_inv_ι O.2).symm
  rw [hiso, pb_comp_apply, h0, map_zero]

end Classes

section Existence

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
  [IsProper π] [Flat π] [GeometricallyIntegral π] {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  (D : Rep R C.Q 1) {W : (pullback π D.p).IdealSheafData}
  (hW : ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
      (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k),
      W.comap (ptMap π D.p k hk) = LinSys.FOf L D k hk hP)

omit [IsNoetherianRing R] [IsProper π] [Flat π] in
include he hW in
/-- **Local existence:** over an affine base where `O(E) ≅ L_B`, the divisor `E` is the pullback
of the universal divisor along a point of the Grassmannian. -/
theorem exists_point_of_affine {B : Type u} [CommRing B] [Algebra R B]
    (E : (pullback π (specMap R B)).IdealSheafData)
    (hE : IsRelativeEffectiveCartierIdeal (pullback.snd π (specMap R B)) E)
    (hcl : dcl E hE.1 = Group.pullback (pullback.fst π (specMap R B)) L.classOf) :
    ∃ (k : Spec (.of B) ⟶ D.Gr) (hk : k ≫ D.p = specMap R B),
      W.comap (ptMap π D.p k hk) = E := by
  let DE : EffectiveCartierDivisor (pullback π (specMap R B)) := ⟨E, hE.1⟩
  have hiso : Nonempty (DE.lineBundle.obj ≅ (pbLB (pullback.fst π (specMap R B)) L).obj) := by
    rw [← LineBundle.classOf_eq_iff]
    rw [Group.pullback_lineBundle_classOf] at hcl
    exact hcl
  obtain ⟨eiso⟩ := hiso
  let σ' : Γ((pbLB (pullback.fst π (specMap R B)) L).obj, ⊤) :=
    eiso.hom.app ⊤ DE.canonicalSection
  have hσ' : zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) σ' = E :=
    (zeroIdeal_iso DE.lineBundle DE.canonicalSection eiso).trans (zeroIdeal_canonicalSection DE)
  let v := (C.homEquivSections B).symm σ'
  have hv0 : C.homEquivSections B v = σ' := Equiv.apply_symm_apply _ _
  have hzv : zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v) = E := by
    rw [hv0, hσ']
  have hspan := span_range_of_isRelativeEffective e he C v (hzv ▸ hE)
  exact ⟨(D.pt B (linePt v hspan)).1, (D.pt B (linePt v hspan)).2,
    (comap_ptMap_linePt e he C D hW v hspan).trans hzv⟩

omit [IsNoetherianRing R] [IsProper π] [Flat π] [GeometricallyIntegral π] in
lemma isOpenImmersion_mapX {T T' : Scheme.{u}} {s : T ⟶ Spec (.of R)} {s' : T' ⟶ Spec (.of R)}
    (h : T' ⟶ T) [IsOpenImmersion h] (w : h ≫ s = s') : IsOpenImmersion (mapX π h w) := by
  unfold mapX
  infer_instance

omit [IsNoetherianRing R] [IsProper π] [Flat π] [GeometricallyIntegral π] in
lemma range_mapX {T T' : Scheme.{u}} {s : T ⟶ Spec (.of R)} {s' : T' ⟶ Spec (.of R)}
    (h : T' ⟶ T) (w : h ≫ s = s') :
    Set.range (mapX π h w) = pullback.snd π s ⁻¹' Set.range h := by
  rw [mapX, Scheme.Pullback.range_map]
  simp

set_option maxHeartbeats 1000000 in
include he hW in
/-- **Existence:** every divisor of the linear system over a locally noetherian test is the
pullback of the universal divisor along a point of the Grassmannian. -/
theorem exists_point {T' : Scheme.{u}} [IsLocallyNoetherian T'] (t' : T' ⟶ Spec (.of R))
    (E : (pullback π t').IdealSheafData)
    (hE : IsRelativeEffectiveCartierIdeal (pullback.snd π t') E) (n' : Group T')
    (hcl : dcl E hE.1 = Group.pullback (pullback.fst π t') L.classOf +
      Group.pullback (pullback.snd π t') n') :
    ∃ (k : T' ⟶ D.Gr) (hk : k ≫ D.p = t'), W.comap (mapX π k hk) = E := by
  let I := {O : T'.affineOpens // Group.pullback (affPt O) n' = 0}
  -- local points
  have hloc : ∀ O : I, letI := affAlg t' O.1
      ∃ (k : Spec Γ(T', O.1.1) ⟶ D.Gr) (hk : k ≫ D.p = specMap R Γ(T', O.1.1)),
        W.comap (ptMap π D.p k hk) = E.comap (mapX π (affPt O.1) (affPt_comp t' O.1)) := by
    intro O
    let _ := affAlg t' O.1
    have : IsNoetherianRing Γ(T', O.1.1) := IsLocallyNoetherian.component_noetherian O.1
    have hw := affPt_comp t' O.1
    obtain ⟨hE', hcl'⟩ := PicardHilbertPiecesReduction.divBC π
      RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange
      (affPt O.1) hw E hE
    have hcl'' : dcl (E.comap (mapX π (affPt O.1) hw)) hE'.1 =
        Group.pullback (pullback.fst π (specMap R Γ(T', O.1.1))) L.classOf := by
      rw [hcl', hcl, map_add, PicardHilbertPiecesReduction.pb_mapX_fst, ← pb_comp_apply,
        PicardHilbertPiecesReduction.mapX_snd, pb_comp_apply, O.2, map_zero, add_zero]
    exact exists_point_of_affine e he C D hW _ hE' hcl''
  choose kO hkO hkOE using hloc
  -- the open cover by affine opens on which `n'` is trivial
  have hcov : ∀ z : T', ∃ O : I, z ∈ Set.range (affPt O.1) := by
    intro z
    obtain ⟨O, hzO, hO⟩ := exists_affine_pullback_eq_zero n' z
    exact ⟨⟨O, hO⟩, by rw [range_affPt]; exact hzO⟩
  let 𝒱 : T'.OpenCover := Scheme.Cover.mkOfCovers I (fun O => Spec Γ(T', O.1.1))
    (fun O => affPt O.1) (fun z => by
      obtain ⟨O, y, hy⟩ := hcov z
      exact ⟨O, y, hy⟩) (fun _ => inferInstance)
  -- compatibility on overlaps, by injectivity
  have hcompat : ∀ O₁ O₂ : I, pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ kO O₁ =
      pullback.snd (affPt O₁.1) (affPt O₂.1) ≫ kO O₂ := by
    intro O₁ O₂
    let _ := affAlg t' O₁.1
    let _ := affAlg t' O₂.1
    have : IsNoetherianRing Γ(T', O₁.1.1) := IsLocallyNoetherian.component_noetherian O₁.1
    have hc : pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ affPt O₁.1 =
        pullback.snd (affPt O₁.1) (affPt O₂.1) ≫ affPt O₂.1 := pullback.condition
    have hw₁ := affPt_comp t' O₁.1
    have hw₂ := affPt_comp t' O₂.1
    have w₁ : pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ specMap R Γ(T', O₁.1.1) =
        pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ affPt O₁.1 ≫ t' := by rw [hw₁]
    have w₂ : pullback.snd (affPt O₁.1) (affPt O₂.1) ≫ specMap R Γ(T', O₂.1.1) =
        pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ affPt O₁.1 ≫ t' := by
      rw [← hw₂, ← Category.assoc, ← hc, Category.assoc]
    have hk₁ : (pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ kO O₁) ≫ D.p =
        pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ affPt O₁.1 ≫ t' := by
      rw [Category.assoc, hkO, w₁]
    have hk₂ : (pullback.snd (affPt O₁.1) (affPt O₂.1) ≫ kO O₂) ≫ D.p =
        pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ affPt O₁.1 ≫ t' := by
      rw [Category.assoc, hkO, w₂]
    refine eq_of_comap_mapX_eq e he C D hW _ _ hk₁ hk₂ ?_
    have e₁ : mapX π (pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ kO O₁) hk₁ =
        mapX π (pullback.fst (affPt O₁.1) (affPt O₂.1)) w₁ ≫ ptMap π D.p (kO O₁) (hkO O₁) :=
      (mapX_comp π (kO O₁) (hkO O₁) _ w₁).symm
    have e₂ : mapX π (pullback.snd (affPt O₁.1) (affPt O₂.1) ≫ kO O₂) hk₂ =
        mapX π (pullback.snd (affPt O₁.1) (affPt O₂.1)) w₂ ≫ ptMap π D.p (kO O₂) (hkO O₂) :=
      (mapX_comp π (kO O₂) (hkO O₂) _ w₂).symm
    have f₁ : mapX π (pullback.fst (affPt O₁.1) (affPt O₂.1)) w₁ ≫ mapX π (affPt O₁.1) hw₁ =
        mapX π (pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ affPt O₁.1) rfl :=
      mapX_comp π (affPt O₁.1) hw₁ _ w₁
    have f₂ : mapX π (pullback.snd (affPt O₁.1) (affPt O₂.1)) w₂ ≫ mapX π (affPt O₂.1) hw₂ =
        mapX π (pullback.fst (affPt O₁.1) (affPt O₂.1) ≫ affPt O₁.1) rfl :=
      (mapX_comp π (affPt O₂.1) hw₂ _ w₂).trans (mapX_congr π hc.symm _ _)
    rw [e₁, e₂, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hkOE, hkOE,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, f₁, f₂]
  let k : T' ⟶ D.Gr := 𝒱.glueMorphisms kO (fun O₁ O₂ => hcompat O₁ O₂)
  have hkι : ∀ O : I, affPt O.1 ≫ k = kO O :=
    fun O => 𝒱.ι_glueMorphisms kO (fun O₁ O₂ => hcompat O₁ O₂) O
  have hk : k ≫ D.p = t' := by
    refine 𝒱.hom_ext _ _ fun O => ?_
    change affPt O.1 ≫ k ≫ D.p = affPt O.1 ≫ t'
    let _ := affAlg t' O.1
    rw [← Category.assoc, hkι, hkO, affPt_comp]
  refine ⟨k, hk, ?_⟩
  have hopen : ∀ O : I, IsOpenImmersion
      (letI := affAlg t' O.1; mapX π (affPt O.1) (affPt_comp t' O.1)) :=
    fun O => isOpenImmersion_mapX (affPt O.1) _
  refine Langlands.AlgebraicGeometry.IdealSheafGluing.eq_of_comap_eq'
    (fun O : I => letI := affAlg t' O.1; mapX π (affPt O.1) (affPt_comp t' O.1)) ?_ fun O => ?_
  · intro y
    obtain ⟨O, w, hw⟩ := hcov ((pullback.snd π t').base y)
    refine ⟨O, ?_⟩
    rw [range_mapX]
    exact ⟨w, hw⟩
  · let _ := affAlg t' O.1
    have g₁ : mapX π (affPt O.1) (affPt_comp t' O.1) ≫ mapX π k hk =
        ptMap π D.p (kO O) (hkO O) :=
      (mapX_comp π k hk (affPt O.1) (affPt_comp t' O.1)).trans (mapX_congr π (hkι O) _ (hkO O))
    change (W.comap (mapX π k hk)).comap (mapX π (affPt O.1) (affPt_comp t' O.1)) =
      E.comap (mapX π (affPt O.1) (affPt_comp t' O.1))
    rw [← Scheme.IdealSheafData.comap_comp, g₁, hkOE]

end Existence

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
