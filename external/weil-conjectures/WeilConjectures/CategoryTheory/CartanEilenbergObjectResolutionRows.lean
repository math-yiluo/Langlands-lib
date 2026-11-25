/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergBoundaryProjection
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions

/-! # Alternating resolutions of the object-level rows

Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--3
(blueprint: lem-sp-cartan-eilenberg-object-resolution-rows).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- Resolve the boundary/cycle/homology short exact sequences. This makes no
choice of resolutions of the terms of K, nor of the cycle/term/next-boundary rows.

Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--3;
Tag 013T, prescribed-end horseshoe lemma
(blueprint: lem-sp-cartan-eilenberg-object-resolution-rows).

Proof: The image inclusion of d^(p-1) factors through Z^p since d^(p-1)d^p=0.
The resulting sequence 0 -> B^p -> Z^p -> H^p -> 0 is short exact, because
homology is the cokernel of the map from boundaries to cycles. Choose resolutions
of B^p and H^p independently for every integer p. For p<=0 the boundary object is
zero, since K^(p-1) is zero; use its single-degree-zero resolution. For p<0 the
homology object is zero, since K^p is zero; use its single-degree-zero resolution.
Apply the prescribed-end horseshoe lemma in each degree p to these two chosen
resolutions. It produces a resolution of Z^p and maps w and x with both displayed
augmentation squares and degreewise short exactness. Degreewise short exactness
implies short exactness in the category of complexes. At p<0 both end resolution
complexes are zero. The short exact row therefore forces the middle resolution
complex to be zero too. At p=0 only the boundary resolution is zero: the resulting
map from the cycle resolution to the homology resolution is an isomorphism, as
required by H^0=Z^0. No recursion or prescribed initial cycle resolution is needed
for this existence statement: each boundary resolution will later be reused in
the cycle/term row at the preceding degree. -/
theorem exists_cartanEilenberg_object_resolution_rows
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex B ℤ) (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) :
    ∃ (IZ : ∀ p, InjectiveResolution (K.cycles p))
      (ID : ∀ p, InjectiveResolution (image (K.d (p - 1) p)))
      (IH : ∀ p, InjectiveResolution (K.homology p))
      (w : ∀ p, (ID p).cocomplex ⟶ (IZ p).cocomplex)
      (x : ∀ p, (IZ p).cocomplex ⟶ (IH p).cocomplex),
      (∀ p, p < 0 → IsZero (IZ p).cocomplex) ∧
      (∀ p, p ≤ 0 → IsZero (ID p).cocomplex) ∧
      (∃ hwx : ∀ p, w p ≫ x p = 0,
        ∀ p, (ShortComplex.mk (w p) (x p) (hwx p)).ShortExact) ∧
      (∀ p, (CochainComplex.single₀ B).map (cartanEilenbergBoundaryInclusion K p) ≫
        (IZ p).ι = (ID p).ι ≫ w p) ∧
      (∀ p, (CochainComplex.single₀ B).map (K.homologyπ p) ≫ (IH p).ι =
        (IZ p).ι ≫ x p) := by
  classical
  let b := cartanEilenbergBoundaryInclusion K
  have hb (p : ℤ) : b p ≫ K.homologyπ p = 0 := by
    apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
    have hf : factorThruImage (K.d (p - 1) p) ≫ b p = K.toCycles (p - 1) p := by
      apply (cancel_mono (K.iCycles p)).1
      simp [b]
    rw [← Category.assoc, hf]
    simp
  let T (p : ℤ) := ShortComplex.mk (b p) (K.homologyπ p) (hb p)
  have hT (p : ℤ) : (T p).ShortExact := by
    have he : (ShortComplex.mk (K.toCycles (p - 1) p) (K.homologyπ p)
        (K.toCycles_comp_homologyπ (p - 1) p)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (p - 1) p (by simp))
    let φ : ShortComplex.mk (K.toCycles (p - 1) p) (K.homologyπ p)
        (K.toCycles_comp_homologyπ (p - 1) p) ⟶ T p :=
      { τ₁ := factorThruImage (K.d (p - 1) p)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          dsimp [T]
          apply (cancel_mono (K.iCycles p)).1
          simp [b]
        comm₂₃ := by simp [T] }
    have hm : Mono (T p).f := by
      apply mono_of_mono_fac (cartanEilenbergBoundaryInclusion_fac K p)
    exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 he
            mono_f := hm
            epi_g := inferInstance }
  have hd (p : ℤ) (hp : p ≤ 0) : IsZero (image (K.d (p - 1) p)) :=
    IsZero.of_epi (factorThruImage (K.d (p - 1) p)) (hK (p - 1) (by omega))
  have hh (p : ℤ) (hp : p < 0) : IsZero (K.homology p) :=
    (K.sc p).isZero_homology_of_isZero_X₂ (hK p hp)
  let ID (p : ℤ) : InjectiveResolution (image (K.d (p - 1) p)) :=
    if hp : p ≤ 0 then
      let _ := (hd p hp).injective
      InjectiveResolution.self _
    else InjectiveResolution.of _
  let IH (p : ℤ) : InjectiveResolution (K.homology p) :=
    if hp : p < 0 then
      let _ := (hh p hp).injective
      InjectiveResolution.self _
    else InjectiveResolution.of _
  have hdneg (p : ℤ) (hp : p ≤ 0) : IsZero (ID p).cocomplex := by
    dsimp [ID]
    rw [dite_eq_left hp]
    exact Functor.map_isZero (CochainComplex.single₀ B) (hd p hp)
  have hhneg (p : ℤ) (hp : p < 0) : IsZero (IH p).cocomplex := by
    dsimp [IH]
    rw [dite_eq_left hp]
    exact Functor.map_isZero (CochainComplex.single₀ B) (hh p hp)
  have hs (p : ℤ) := InjectiveResolution.exists_horseshoe_prescribed_resolutions
    (T p) (hT p) (ID p) (IH p)
  choose IZ w x hw hx hwx hrows using hs
  have hex (p : ℤ) := HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk (w p) (x p) (hwx p)) (fun q ↦ (hrows p q).1)
  refine ⟨IZ, ID, IH, w, x, ?_, hdneg, ⟨hwx, hex⟩, fun p ↦ (hw p).symm, fun p ↦ (hx p).symm⟩
  intro p hp
  have hi : IsIso (w p) := (hex p).isIso_f_iff.mpr (hhneg p hp)
  exact IsZero.of_iso (hdneg p (by omega)) (asIso (w p)).symm

end CategoryTheory
