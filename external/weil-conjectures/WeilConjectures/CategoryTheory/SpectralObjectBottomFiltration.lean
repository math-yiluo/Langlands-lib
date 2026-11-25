/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration


public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.CategoryTheory.SpectralObjectBottomPageCompatibility
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Bottom edge factorization for a first-quadrant spectral object

Source: Stacks Project, Tags 012K, 015J and 015N; image filtration of the abutment.
(blueprint: lem-sc-spectral-object-bottom-filtration)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

private theorem bottomPageMap_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : SpectralObject C EInt) [Y.IsFirstQuadrant] (p : ℕ) :
    Mono (Y.bottomPageMap p (p + 2) (by omega)) := by
  have := Y.isIso_H_map_twoδ₁Toδ₀' p (p + 1) rfl ⊥ (0 : ℤ) (p + 2 - 1 : ℤ)
    bot_le (WithBotTop.coe_le_coe.2 (by omega))
    (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl _)
    (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl _)
  have := Y.isIso_H_map_twoδ₂Toδ₁ (p - 1) p (by omega)
    (homOfLE (bot_le : (⊥ : EInt) ≤ (p + 2 - 1 : ℤ)))
    (homOfLE (le_top : ((p + 2 - 1 : ℤ) : EInt) ≤ ⊤))
    (homOfLE bot_le) (Subsingleton.elim _ _)
    (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (WithBotTop.coe_lt_coe.2 (by omega)))
    (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (WithBotTop.coe_lt_coe.2 (by omega)))
  dsimp only [bottomPageMap]
  infer_instance

private theorem bottomPageMap_two
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : SpectralObject C EInt) [Y.IsFirstQuadrant] (p : ℕ) :
    Y.bottomPageMap p 2 (by omega) =
      (Y.E₂SpectralSequenceNatPageTwoXIso p 0).hom ≫ Y.bottomEdge p := by
  dsimp only [bottomPageMap, bottomEdge, E₂SpectralSequenceNatPageTwoXIso,
    spectralSequenceFirstPageXIso, Iso.trans_hom]
  simp only [Nat.add_zero, Int.reduceSub, Category.assoc]
  congr 1
  have hE :
      (Y.EIsoH (homOfLE (show ((0 : ℤ) : EInt) ≤ (1 : ℤ) by simp))
        (p - 1) p (p + 1)).hom =
      Y.ιE (𝟙 ((0 : ℤ) : EInt)) (homOfLE (by simp)) (𝟙 ((1 : ℤ) : EInt))
        (p - 1) p (p + 1) ≫
      Y.fromOpcycles (homOfLE (show ((0 : ℤ) : EInt) ≤ (1 : ℤ) by simp))
        (𝟙 _) (homOfLE (by simp)) (by simp) p := by
    rw [← Y.EIsoH_hom_opcyclesIsoH_inv (p - 1) p (p + 1) (by omega) rfl]
    simp only [Category.assoc, opcyclesIsoH_inv_hom_id, Category.comp_id]
  rw [hE]
  simp only [Category.assoc]
  congr 2


end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory

private noncomputable def cokernel_ofLE_congr
    {C : Type u} [Category.{v} C] [Abelian C] {Z : C}
    (S T S' T' : Subobject Z) (h : S ≤ T) (h' : S' ≤ T')
    (hs : S = S') (ht : T = T') :
    cokernel (Subobject.ofLE S T h) ≅ cokernel (Subobject.ofLE S' T' h') := by
  subst S' T'
  exact Iso.refl _

private lemma transported_subobject_eq
    {C : Type u} [Category.{v} C] [Abelian C] {Z Z' : C}
    (e : Z ≅ Z') (S : Subobject Z) :
    (Subobject.«exists» e.hom).obj S = Subobject.mk (S.arrow ≫ e.hom) := by
  rw [Subobject.exists_iso_map]
  conv_lhs => rw [← Subobject.mk_arrow S, Subobject.map_mk]

private noncomputable def cokernel_ofLE_transport
    {C : Type u} [Category.{v} C] [Abelian C] {Z Z' : C}
    (e : Z ≅ Z') (S T : Subobject Z) (h : S ≤ T) :
    cokernel (Subobject.ofLE
      (Subobject.mk (S.arrow ≫ e.hom)) (Subobject.mk (T.arrow ≫ e.hom))
      (Subobject.mk_le_mk_of_comm (Subobject.ofLE S T h) (by simp))) ≅
      cokernel (Subobject.ofLE S T h) := by
  refine cokernel.mapIso _ _ (Subobject.underlyingIso _) (Subobject.underlyingIso _) ?_
  simp [← cancel_mono (T.arrow ≫ e.hom)]

private theorem graded_comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : Abelian.SpectralObject C EInt) [Y.IsFirstQuadrant]
    (H : ℕ → C)
    (h : ∀ n : ℕ, (Y.H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ H n)
    (T : ∀ n : ℕ, DecreasingFiltration (H n))
    (hT : ∀ (n : ℕ) (i : ℤ), (T n).step i =
      (Subobject.«exists» (h n).hom).obj (Y.imageFiltration n ((n : ℤ) + 1 - i)))
    (p q : ℕ) :
    Nonempty ((T (p + q)).gradedPiece p ≅ Y.E₂SpectralSequenceNat.pageInfinity (p, q)) := by
  classical
  let n : ℤ := (p + q : ℕ)
  let raw : DecreasingFiltration
      ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) :=
    { F := fun i ↦ Y.imageFiltration n (n + 1 - i)
      F_succ_le i := Y.imageFiltration_mono n (by omega) }
  have hs : raw.step (p : ℤ) = Y.imageFiltration n ((q : ℤ) + 1) := by
    dsimp [raw, n, DecreasingFiltration.step]
    congr 1
    omega
  have ht : raw.step ((p : ℤ) + 1) = Y.imageFiltration n (q : ℤ) := by
    dsimp [raw, n, DecreasingFiltration.step]
    congr 1
    omega
  let rawiso : raw.gradedPiece p ≅ Y.E₂SpectralSequenceNat.pageInfinity (p, q) :=
    cokernel_ofLE_congr _ _ _ _ _ (Y.imageFiltration_mono n (by omega)) ht hs ≪≫
      (Y.nonempty_cokernel_ofLE_imageFiltration_iso n q (q + 1) rfl
        (Y.imageFiltration_mono n (by omega))).some ≪≫
      (Y.nonempty_pageInfinity_iso p q n q (q + 1) (by simp [n]) rfl rfl).some.symm
  have hstep (i : ℤ) : (T (p + q)).step i =
      Subobject.mk ((raw.step i).arrow ≫ (h (p + q)).hom) := by
    rw [hT, transported_subobject_eq]
  exact ⟨cokernel_ofLE_congr _ _ _ _ _ _ (hstep (p + 1)) (hstep p) ≪≫
    cokernel_ofLE_transport (h (p + q)) (raw.step (p + 1)) (raw.step p)
      (raw.antitone_step (by omega)) ≪≫ rawiso⟩

/-- Compare the graded pieces and bottom edge of the image filtration from a first-quadrant
spectral object, after any specified isomorphism of its abutment. The filtration
and its bounds are constructed separately; this theorem supplies only the
graded comparisons and their compatibility with the iterated bottom projection.

Source: Stacks Project, Tags 012K, 015J and 015N.
(blueprint: lem-sc-spectral-object-bottom-filtration)

Proof: The existing spectral-object abutment identifies raw consecutive image
quotients with the stable page. Transport these cokernel isomorphisms by h and
hT to obtain graded comparisons. Define the bottom-page map by the page
comparison, iota-E, fromOpcycles, the inverse H(bottom,c) -> H(0,c), and the
map to H(bottom,top). At page two it is the interval comparison followed by
bottomEdge; at page p+2 it is monic by first-quadrant vanishing. The local
cycles-to-homology compatibility square and ht identify its successor
composites with t. Integer induction using hb2 and hbt gives b followed by
the page-r map equal to the page-two map; the same induction proves b epi.
The epi-mono factorization therefore identifies the stable bottom page with
the image of bottomEdge, namely imageFiltration(p,1). Transport this mono
through h to obtain k. Since T_p^(p+1) is bottom, the quotient projection is
invertible. On the bottom row choose g to be that inverse projection followed
by k inverse; off the bottom row use the previously constructed graded
comparisons. The quotient identity follows by cancellation and the bottom
factorization follows from the induction. All constructions also apply at
p=0, where the first page and stable bottom page are both page two.
-/
theorem exists_spectral_object_bottom_filtration
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : Abelian.SpectralObject C EInt) [Y.IsFirstQuadrant]
    (H : ℕ → C)
    (h : ∀ n : ℕ, (Y.H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ H n)
    (T : ∀ n : ℕ, DecreasingFiltration (H n))
    (hT : ∀ (n : ℕ) (i : ℤ), (T n).step i =
      (Subobject.«exists» (h n).hom).obj (Y.imageFiltration n ((n : ℤ) + 1 - i)))
    (t : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      (Y.E₂SpectralSequenceNat.page r hr).X (p, 0) ⟶
        (Y.E₂SpectralSequenceNat.page (r + 1) (by omega)).X (p, 0))
    (ht : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      (Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0) ≫ t p r hr =
        (Y.E₂SpectralSequenceNat.page r hr).homologyπ (p, 0) ≫
          (Y.E₂SpectralSequenceNat.iso r (r + 1) (p, 0) rfl hr).hom)
    (b : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      (Y.E₂SpectralSequenceNat.page 2).X (p, 0) ⟶
        (Y.E₂SpectralSequenceNat.page r hr).X (p, 0))
    (hb2 : ∀ p, b p 2 (by omega) = 𝟙 _)
    (hbt : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      b p (r + 1) (by omega) = b p r hr ≫ t p r hr) :
    ∃ g : ∀ p q : ℕ, (T (p + q)).gradedPiece p ≅
        Y.E₂SpectralSequenceNat.pageInfinity (p, q),
      ∃ k : ∀ p : ℕ, Y.E₂SpectralSequenceNat.pageInfinity (p, 0) ≅
          ((T p).step p : C),
        (∀ p, cokernel.π (Subobject.ofLE ((T p).step (p + 1))
          ((T p).step p) ((T p).antitone_step (by omega))) ≫
            (g p 0).hom = (k p).inv) ∧
        (∀ p : ℕ, (Y.E₂SpectralSequenceNatPageTwoXIso p 0).hom ≫
          Y.bottomEdge p ≫ (h p).hom =
            b p (p + 2) (by omega) ≫ (k p).hom ≫ ((T p).step p).arrow) := by
  classical
  have hi (p : ℕ) (r : ℤ) (hr : 2 ≤ r) :
      IsIso ((Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0)) := by
    apply (Y.E₂SpectralSequenceNat.page r hr).isIso_iCycles (p, 0) _ rfl
    apply (Y.E₂SpectralSequenceNat.page r hr).shape
    simp only [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  have ht_epi (p : ℕ) (r : ℤ) (hr : 2 ≤ r) : Epi (t p r hr) := by
    have := hi p r hr
    have hcomp : Epi ((Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0) ≫ t p r hr) :=
      (ht p r hr) ▸ inferInstance
    exact epi_of_epi ((Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0)) (t p r hr)
  have hb_epi (p : ℕ) (r : ℤ) (hr : 2 ≤ r) : Epi (b p r hr) := by
    induction r, hr using Int.leInduction with
    | base => rw [hb2]; infer_instance
    | succ r hr ih =>
      have := ht_epi p r hr
      rw [hbt p r hr]
      infer_instance
  have hstep (p : ℕ) (r : ℤ) (hr : 2 ≤ r) :
      t p r hr ≫ Y.bottomPageMap p (r + 1) (by omega) = Y.bottomPageMap p r hr := by
    have := hi p r hr
    apply (cancel_epi ((Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0))).mp
    rw [← Category.assoc, ht, Category.assoc, Y.bottomPageMap_compatibility]
  have hfac (p : ℕ) (r : ℤ) (hr : 2 ≤ r) :
      b p r hr ≫ Y.bottomPageMap p r hr = Y.bottomPageMap p 2 (by omega) := by
    induction r, hr using Int.leInduction with
    | base => simp [hb2]
    | succ r hr ih => rw [hbt p r hr, Category.assoc, hstep, ih]
  have hm (p : ℕ) : Mono (Y.bottomPageMap p (p + 2) (by omega)) :=
    Y.bottomPageMap_mono p
  have hp2 (p : ℕ) : (2 : ℤ) ≤ p + 2 := by omega
  have hraw (p : ℕ) :
      Subobject.mk (Y.bottomPageMap p (p + 2) (hp2 p)) = Y.imageFiltration p 1 := by
    have := hm p
    have := hb_epi p (p + 2) (by omega)
    rw [← imageSubobject_mono, ← imageSubobject_comp_of_epi (b p (p + 2) (hp2 p)),
      hfac, Y.bottomPageMap_two, imageSubobject_iso_comp, Y.imageSubobject_bottomEdge]
  have hTk (p : ℕ) : (T p).step p =
      Subobject.mk (Y.bottomPageMap p (p + 2) (by omega) ≫ (h p).hom) := by
    have := hm p
    rw [hT, show (p : ℤ) + 1 - p = 1 by omega, ← hraw]
    rw [Subobject.exists_iso_map, Subobject.map_mk]
  let k (p : ℕ) : Y.E₂SpectralSequenceNat.pageInfinity (p, 0) ≅ ((T p).step p : C) :=
    (Subobject.isoOfEqMk _ _ (hTk p)).symm
  have hk (p : ℕ) :
      (k p).hom ≫ ((T p).step p).arrow =
        Y.bottomPageMap p (p + 2) (by omega) ≫ (h p).hom := by
    simp [k]
  have hzero (p : ℕ) : (T p).step (p + 1) = ⊥ := by
    rw [hT, Y.imageFiltration_eq_bot _ _ (by omega)]
    rw [Subobject.exists_iso_map, Subobject.map_bot]
  have hπ (p : ℕ) : IsIso (cokernel.π (Subobject.ofLE ((T p).step (p + 1))
      ((T p).step p) ((T p).antitone_step (by omega)))) := by
    apply cokernel.π_of_zero
    apply (cancel_mono ((T p).step p).arrow).mp
    simp only [Subobject.ofLE_arrow, zero_comp]
    rw [hzero]
    simp
  let g (p q : ℕ) : (T (p + q)).gradedPiece p ≅
      Y.E₂SpectralSequenceNat.pageInfinity (p, q) :=
    if hq : q = 0 then by
      subst q
      simpa only [Nat.add_zero, DecreasingFiltration.gradedPiece,
        DecreasingFiltration.gr, DecreasingFiltration.step] using
        (@asIso _ _ _ _ (cokernel.π (Subobject.ofLE ((T p).step (p + 1))
          ((T p).step p) ((T p).antitone_step (by omega)))) (hπ p)).symm ≪≫ (k p).symm
    else (graded_comparison Y H h T hT p q).some
  refine ⟨g, k, ?_, ?_⟩
  · intro p
    simp [g]
  · intro p
    rw [← Category.assoc, ← Y.bottomPageMap_two, ← hfac p (p + 2) (by omega)]
    simp only [Category.assoc, hk]

end CategoryTheory
