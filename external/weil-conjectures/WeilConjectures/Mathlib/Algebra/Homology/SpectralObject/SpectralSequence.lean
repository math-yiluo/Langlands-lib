/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.Algebra.Homology.SpectralObject.EpiMono
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Convergence of the spectral sequence of a first quadrant spectral object

Let `Y : SpectralObject C EInt` be a first quadrant spectral object in an abelian category
(`[Y.IsFirstQuadrant]`), and write `hⁿ(a, b)` for `(Y.H n).obj (mk₁ (homOfLE _ : a ≤ b))`.
Mathlib constructs the first quadrant `E₂` spectral sequence `Y.E₂SpectralSequenceNat`.
In this file we compute its `E₂`-page and show that it converges to `hⁿ(⊥, ⊤)`.

The filtration of `hⁿ(⊥, ⊤)` is the image filtration: `Fᵖ` is the image of
`hⁿ(⊥, n + 1 - p) ⟶ hⁿ(⊥, ⊤)`, realised as the monomorphism `Y.fromOpcycles` out of
`opZⁿ(⊥ ≤ n + 1 - p, n + 1 - p ≤ ⊤)`. The successive quotients are computed using the short
exact sequence `Y.shortComplexOpcyclesThreeδ₂Toδ₁_shortExact`, and identified with the
`E∞`-terms using `Y.spectralSequencePageXIso` together with the vanishing of `hⁿ` outside
the first quadrant.

## Main definitions and results

- `CategoryTheory.Abelian.SpectralObject.E₂SpectralSequenceNatPageTwoXIso`: the isomorphism
  `E₂^{p, q} ≅ h^{p + q}(q, q + 1)`.
- `CategoryTheory.Abelian.SpectralObject.E₂SpectralSequenceNatAbutment`: the abutment of
  `Y.E₂SpectralSequenceNat` to `n ↦ hⁿ(⊥, ⊤)`.
- `CategoryTheory.Abelian.SpectralObject.abutsTo_E₂SpectralSequenceNat`: the spectral sequence
  `Y.E₂SpectralSequenceNat` abuts to `n ↦ hⁿ(⊥, ⊤)`.
- `CategoryTheory.Abelian.SpectralObject.bottomEdge`,
  `CategoryTheory.Abelian.SpectralObject.leftEdge`: the edge maps
  `E₂^{n, 0} = hⁿ(0, 1) ⟶ hⁿ(⊥, ⊤)` and `hⁿ(⊥, ⊤) ⟶ hⁿ(n, n + 1) = E₂^{0, n}`, which are
  natural in `Y` (`bottomEdge_naturality`, `leftEdge_naturality`).
-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C : Type*} [Category* C] [Abelian C] (Y : SpectralObject C EInt)

/-- The subobject `Fᵃ` of `hⁿ(⊥, ⊤)` given by the image of `hⁿ(⊥, a) ⟶ hⁿ(⊥, ⊤)`,
realised as the mono `opZⁿ(⊥ ≤ a, a ≤ ⊤) ⟶ hⁿ(⊥, ⊤)`. -/
noncomputable def imageFiltration (n : ℤ) (a : ℤ) :
    Subobject ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) :=
  Subobject.mk (Y.fromOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ a))
    (homOfLE (le_top : (a : EInt) ≤ ⊤)) _ rfl n)

/-- Any morphism `opZ^n(⊥ ≤ a, a ≤ ⊤) ⟶ opZ^n(⊥ ≤ b, b ≤ ⊤)` induced by a morphism of
composable arrows is compatible with the monomorphisms into `hⁿ(⊥, ⊤)`. -/
lemma opcyclesMap_fromOpcycles_bot_top (n : ℤ) (a b : EInt)
    (α : mk₂ (homOfLE (bot_le : ⊥ ≤ a)) (homOfLE (le_top : a ≤ ⊤)) ⟶
      mk₂ (homOfLE (bot_le : ⊥ ≤ b)) (homOfLE (le_top : b ≤ ⊤))) :
    Y.opcyclesMap _ _ _ _ α n ≫ Y.fromOpcycles _ _ _ rfl n = Y.fromOpcycles _ _ _ rfl n := by
  refine (Y.opcyclesMap_fromOpcycles (homOfLE (bot_le : ⊥ ≤ a))
    (homOfLE (le_top : a ≤ ⊤)) (homOfLE (bot_le : ⊥ ≤ b))
    (homOfLE (le_top : b ≤ ⊤)) _ rfl _ rfl α (𝟙 _) n rfl rfl).trans ?_
  rw [Functor.map_id, Category.comp_id]

/-- The image filtration is increasing in `a` (i.e. decreasing in `p = n + 1 - a`). -/
lemma imageFiltration_mono (n : ℤ) {a b : ℤ} (hab : a ≤ b) :
    Y.imageFiltration n a ≤ Y.imageFiltration n b :=
  Subobject.mk_le_mk_of_comm _ (Y.opcyclesMap_fromOpcycles_bot_top n a b
    (homMk₂ (homOfLE le_rfl) (homOfLE (by simpa using hab)) (homOfLE le_rfl)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)))

/-- The successive quotient `Fᵇ / Fᵃ` (for `b = a + 1`) of the image filtration of `hⁿ(⊥, ⊤)`
is isomorphic to `Eⁿ(⊥ ≤ a ≤ b ≤ ⊤)`. -/
lemma nonempty_cokernel_ofLE_imageFiltration_iso (n a b : ℤ) (hab : a + 1 = b)
    (h : Y.imageFiltration n a ≤ Y.imageFiltration n b) :
    Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
      Y.E (homOfLE (bot_le : (⊥ : EInt) ≤ a)) (homOfLE (show (a : EInt) ≤ b by simp; lia))
        (homOfLE (le_top : (b : EInt) ≤ ⊤)) (n - 1) n (n + 1)) := by
  have hS := Y.shortComplexOpcyclesThreeδ₂Toδ₁_shortExact (homOfLE (bot_le : (⊥ : EInt) ≤ a))
    (homOfLE (show (a : EInt) ≤ b by simp; lia)) (homOfLE (le_top : (b : EInt) ≤ ⊤))
    (homOfLE bot_le) (homOfLE le_top) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (n - 1) n (n + 1)
  refine ⟨cokernel.mapIso _ _ (Subobject.underlyingIso _) (Subobject.underlyingIso _) ?_ ≪≫
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hS.gIsCokernel⟩
  unfold imageFiltration at h ⊢
  rw [Subobject.ofLE_mk_le_mk_of_comm _ (Y.opcyclesMap_fromOpcycles_bot_top n a b
    (threeδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a))
      (homOfLE (show (a : EInt) ≤ b by simp; lia)) (homOfLE (le_top : (b : EInt) ≤ ⊤))
      (homOfLE bot_le) (homOfLE le_top)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)))]
  simp

section

variable [Y.IsFirstQuadrant]

/-- For `n < a`, the image filtration step `Fᵃ` of `hⁿ(⊥, ⊤)` is everything. -/
lemma imageFiltration_eq_top (n a : ℤ) (ha : n < a) : Y.imageFiltration n a = ⊤ := by
  have := Y.isIso_fromOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ a))
    (homOfLE (le_top : (a : EInt) ≤ ⊤)) _ rfl n
    (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (by simpa using ha))
  exact Subobject.mk_eq_top_of_isIso _

/-- For `a ≤ 0`, the image filtration step `Fᵃ` of `hⁿ(⊥, ⊤)` is zero. -/
lemma imageFiltration_eq_bot (n a : ℤ) (ha : a ≤ 0) : Y.imageFiltration n a = ⊥ := by
  rw [imageFiltration, Subobject.mk_eq_bot_iff_zero]
  exact (Y.isZero_opcycles _ _ n
    (Y.isZero₁_of_isFirstQuadrant _ _ _ (by simpa using ha) n)).eq_of_src _ _

/-- The `E∞`-term at `(p, q)` of `Y.E₂SpectralSequenceNat` is isomorphic to
`E^{p + q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)`. -/
lemma nonempty_pageInfinity_iso (p q : ℕ) (n a b : ℤ) (hn : n = p + q) (ha : a = q)
    (hb : b = q + 1) :
    Nonempty (Y.E₂SpectralSequenceNat.pageInfinity (p, q) ≅
      Y.E (homOfLE (bot_le : (⊥ : EInt) ≤ a)) (homOfLE (show (a : EInt) ≤ b by simp; lia))
        (homOfLE (le_top : (b : EInt) ≤ ⊤)) (n - 1) n (n + 1)) := by
  subst hn ha hb
  exact ⟨Y.spectralSequencePageXIso coreE₂CohomologicalNat _ (by push_cast; lia) (p, q)
    (-p : ℤ) q (q + 1 : ℤ) (q + (p + q + 2 : ℕ) - 1 : ℤ) (by dsimp; congr 1; lia) rfl rfl (by simp)
    (p + q - 1) (p + q) (p + q + 1) (by simp) ≪≫
    (Y.isoMapFourδ₁Toδ₀' ⊥ (-p : ℤ) q (q + 1 : ℤ) (q + (p + q + 2 : ℕ) - 1 : ℤ) bot_le
      (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
      (WithBotTop.coe_le_coe.2 (by lia)) _ _ _
      (Y.isZero₁_of_isFirstQuadrant _ _ _ (WithBotTop.coe_le_coe.2 (by lia)) _)).symm ≪≫
    Y.isoMapFourδ₄Toδ₃' ⊥ q (q + 1 : ℤ) (q + (p + q + 2 : ℕ) - 1 : ℤ) ⊤ bot_le
      (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia)) le_top _ _ _
      (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (WithBotTop.coe_lt_coe.2 (by lia)))⟩

/-- The `E₂`-page of the spectral sequence of a first quadrant spectral object:
`E₂^{p, q} ≅ h^{p + q}(q ≤ q + 1)`. -/
noncomputable def E₂SpectralSequenceNatPageTwoXIso (p q : ℕ) :
    (Y.E₂SpectralSequenceNat.page 2).X (p, q) ≅
      (Y.H (p + q : ℕ)).obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))) :=
  Y.spectralSequenceFirstPageXIso coreE₂CohomologicalNat (p, q) _ _ rfl rfl _ (by simp)

/-- The spectral sequence `Y.E₂SpectralSequenceNat` of a first quadrant spectral object abuts to
`n ↦ hⁿ(⊥ ≤ ⊤)`, filtered by the images `Fᵖ` of `hⁿ(⊥ ≤ n + 1 - p) ⟶ hⁿ(⊥ ≤ ⊤)`. -/
noncomputable def E₂SpectralSequenceNatAbutment :
    Y.E₂SpectralSequenceNat.Abutment
      (fun n : ℕ ↦ (Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) where
  filtration n p := Y.imageFiltration n (n + 1 - p)
  filtration_succ_le n p := Y.imageFiltration_mono n (by lia)
  filtration_zero n := Y.imageFiltration_eq_top n _ (by lia)
  filtration_succ_self n := Y.imageFiltration_eq_bot n _ (by lia)
  nonempty_gradedIso n p q hpq :=
    ⟨(Y.nonempty_cokernel_ofLE_imageFiltration_iso _ _ _ (by lia) _).some ≪≫
      (Y.nonempty_pageInfinity_iso p q _ _ _ (by lia) (by lia) (by lia)).some.symm⟩

/-- The spectral sequence `Y.E₂SpectralSequenceNat` of a first quadrant spectral object
converges to `n ↦ hⁿ(⊥ ≤ ⊤)`. -/
theorem abutsTo_E₂SpectralSequenceNat :
    Y.E₂SpectralSequenceNat.AbutsTo
      (fun n : ℕ ↦ (Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) :=
  ⟨Y.E₂SpectralSequenceNatAbutment⟩

/-- For a first quadrant spectral object, the map `hⁿ(⊥, 1) ⟶ hⁿ(0, 1)` is an isomorphism. -/
lemma isIso_H_map_bot_zero_one (n : ℤ) :
    IsIso ((Y.H n).map (twoδ₁Toδ₀' ⊥ ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) bot_le (by simp))) :=
  Y.isIso_H_map_twoδ₁Toδ₀' n (n + 1) rfl _ _ _ _ _
    (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl n)
    (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl (n + 1))

/-- For a first quadrant spectral object, the map `hⁿ(n, n + 1) ⟶ hⁿ(n, ⊤)` is
an isomorphism. -/
lemma isIso_H_map_self_succ_top (n : ℤ) :
    IsIso ((Y.H n).map (twoδ₂Toδ₁' ((n : ℤ) : EInt) ((n + 1 : ℤ) : EInt) ⊤
      (by simp) le_top)) :=
  Y.isIso_H_map_twoδ₂Toδ₁ (n - 1) n (by lia) _ _ _ _
    (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; lia))
    (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp))

/-- The bottom edge map `E₂^{n, 0} = hⁿ(0, 1) ⟶ hⁿ(⊥, ⊤)` of the spectral sequence of a first
quadrant spectral object: the inverse of the isomorphism `hⁿ(⊥, 1) ≅ hⁿ(0, 1)` followed by
the map `hⁿ(⊥, 1) ⟶ hⁿ(⊥, ⊤)`. -/
noncomputable def bottomEdge (n : ℤ) :
    (Y.H n).obj (mk₁ (homOfLE (show ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) by simp))) ⟶
      (Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) :=
  have := Y.isIso_H_map_bot_zero_one n
  inv ((Y.H n).map (twoδ₁Toδ₀' ⊥ ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) bot_le (by simp))) ≫
    (Y.H n).map (twoδ₂Toδ₁' ⊥ ((1 : ℤ) : EInt) ⊤ bot_le le_top)

/-- The left edge map `hⁿ(⊥, ⊤) ⟶ hⁿ(n, n + 1) = E₂^{0, n}` of the spectral sequence of a first
quadrant spectral object: the map `hⁿ(⊥, ⊤) ⟶ hⁿ(n, ⊤)` followed by the inverse of the
isomorphism `hⁿ(n, n + 1) ≅ hⁿ(n, ⊤)`. -/
noncomputable def leftEdge (n : ℤ) :
    (Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ⟶
      (Y.H n).obj (mk₁ (homOfLE (show ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt) by simp))) :=
  have := Y.isIso_H_map_self_succ_top n
  (Y.H n).map (twoδ₁Toδ₀' ⊥ ((n : ℤ) : EInt) ⊤ bot_le le_top) ≫
    inv ((Y.H n).map (twoδ₂Toδ₁' ((n : ℤ) : EInt) ((n + 1 : ℤ) : EInt) ⊤ (by simp) le_top))

/-- The image of the bottom edge map `hⁿ(0, 1) ⟶ hⁿ(⊥, ⊤)` is the smallest possibly nonzero
step `F¹` of the image filtration, i.e. the step of filtration degree `p = n` of the abutment. -/
lemma imageSubobject_bottomEdge (n : ℤ) :
    imageSubobject (Y.bottomEdge n) = Y.imageFiltration n 1 := by
  have := Y.isIso_H_map_bot_zero_one n
  rw [bottomEdge, imageSubobject_iso_comp, imageFiltration, ← imageSubobject_mono,
    ← Y.p_fromOpcycles]
  have : IsIso (Subobject.ofLE _ _ (imageSubobject_comp_le (Y.pOpcycles _ _ n)
      (Y.fromOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((1 : ℤ) : EInt)))
        (homOfLE (le_top : ((1 : ℤ) : EInt) ≤ ⊤)) _ rfl n))) :=
    isIso_of_mono_of_epi _
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ _)) (Subobject.ofLE_arrow _)

variable {Y} in
/-- The bottom edge map is natural in the first quadrant spectral object. -/
lemma bottomEdge_naturality {Y' : SpectralObject C EInt} [Y'.IsFirstQuadrant] (φ : Y ⟶ Y')
    (n : ℤ) :
    (φ.hom n).app _ ≫ Y'.bottomEdge n = Y.bottomEdge n ≫ (φ.hom n).app _ := by
  have := Y.isIso_H_map_bot_zero_one n
  have := Y'.isIso_H_map_bot_zero_one n
  rw [bottomEdge, bottomEdge, Category.assoc, IsIso.eq_inv_comp, NatTrans.naturality_assoc,
    IsIso.hom_inv_id_assoc, NatTrans.naturality]

variable {Y} in
/-- The left edge map is natural in the first quadrant spectral object. -/
lemma leftEdge_naturality {Y' : SpectralObject C EInt} [Y'.IsFirstQuadrant] (φ : Y ⟶ Y')
    (n : ℤ) :
    (φ.hom n).app _ ≫ Y'.leftEdge n = Y.leftEdge n ≫ (φ.hom n).app _ := by
  have := Y.isIso_H_map_self_succ_top n
  have := Y'.isIso_H_map_self_succ_top n
  rw [leftEdge, leftEdge, Category.assoc, ← NatTrans.naturality_assoc]
  congr 1
  rw [IsIso.eq_inv_comp, NatTrans.naturality_assoc, IsIso.hom_inv_id, Category.comp_id]

end

end SpectralObject

end Abelian

end CategoryTheory
