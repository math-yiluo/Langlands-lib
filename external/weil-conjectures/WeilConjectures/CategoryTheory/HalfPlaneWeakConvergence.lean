/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.FinitePageImageQuotient
import WeilConjectures.CategoryTheory.DerivedCoupleExact

/-!
# Canonical quotient maps in half-plane convergence

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, canonical comparison.
(blueprint: lem-sp-half-plane-weak-convergence)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem page_zero (X : BigradedExactCouple C 0) (p q : ℤ)
    (hE : IsZero (X.E p q)) (r : ℕ) : IsZero ((X.pageCouple r).E p q) := by
  induction r with
  | zero => exact hE
  | succ r ih =>
    have : Epi ((X.pageCouple r).derivedEProjection p q) := by
      dsimp [derivedEProjection, derivedE]
      infer_instance
    exact IsZero.of_epi ((X.pageCouple r).derivedEProjection p q)
      (IsZero.of_mono (kernel.ι ((X.pageCouple r).d p q)) ih)

private theorem alpha_iso_left (X : BigradedExactCouple C 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (p q : ℤ) (hp : p ≤ 0) : IsIso (X.alpha p q) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, p = i + 2 := ⟨p - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, q = j - 1 := ⟨q + 1, by omega⟩
  have hker : kernelSubobject (X.alpha (i + 2) (j - 1)) = ⊥ := by
    have hz : X.f i j = 0 := (hE i j (Or.inl (by omega))).eq_zero_of_src _
    exact (X.exact_alpha i j).symm.trans (by rw [hz, imageSubobject_zero])
  have : Mono (X.alpha (i + 2) (j - 1)) :=
    Abelian.mono_of_kernel_ι_eq_zero _ (Subobject.mk_eq_bot_iff_zero.mp hker)
  have him : imageSubobject (X.alpha (i + 2) (j - 1)) = ⊤ := by
    have hz : X.g (i + 2 - 1) (j - 1 + 1) = 0 :=
      (hE _ _ (Or.inl (by omega))).eq_zero_of_tgt _
    simpa only [hz, kernelSubobject_zero] using X.exact_g (i + 2) (j - 1)
  apply (Subobject.isIso_iff_mk_eq_top _).mpr
  rwa [imageSubobject_mono] at him

private theorem cocone_iso_left (X : BigradedExactCouple C 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (A : ∀ n : ℤ, AlphaColimit X n)
    (hA : ∀ n : ℤ, (A n).obj = X.D 0 n)
    (hι : ∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
      eqToHom (by congr 1; omega)) (n p : ℤ) (hp : p ≤ 0) : IsIso ((A n).ι p) := by
  have hzero : IsIso ((A n).ι 0) := by
    have : IsIso ((A n).ι 0 ≫ eqToHom (hA n)) := by
      rw [hι n]
      infer_instance
    exact IsIso.of_isIso_comp_right ((A n).ι 0) (eqToHom (hA n))
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    let t := X.alphaDiagonal n (-((k + 1 : ℕ) : ℤ))
    have ht : IsIso t := by
      dsimp [t, alphaDiagonal]
      have := alpha_iso_left X a hE (-((k : ℤ) + 1) + 1)
        (n - (-((k : ℤ) + 1) + 1)) (by omega)
      infer_instance
    have hc : IsIso (t ≫ (A n).ι (-((k + 1 : ℕ) : ℤ))) := by
      dsimp [t]
      rw [(A n).comm]
      have he : -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) := by omega
      exact Eq.mp (congrArg (fun i : ℤ ↦ IsIso ((A n).ι i)) he.symm) (ih (by omega))
    exact IsIso.of_isIso_comp_left t _

private theorem epi_ofLE_of_eq {D : Type u} [Category.{v} D] {S : D} (B Z : Subobject S)
    (h : B ≤ Z) (heq : B = Z) : Epi (Subobject.ofLE B Z h) := by
  subst Z
  simp only [Subobject.ofLE_refl]
  infer_instance

private theorem graded_zero_of_step_eq {S : C} (F : PBCDecreasingFiltration S)
    (p : ℤ) (h : F.step (p + 1) = F.step p) : IsZero (F.gradedPiece p) := by
  let k := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have : Epi k := epi_ofLE_of_eq _ _ _ h
  exact IsZero.of_epi_eq_zero (cokernel.π k) (zero_of_epi_comp k (cokernel.condition k))

private theorem infinity_zero (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) (h : IsZero (X.E p q)) : IsZero (X.pageInfinity L p q) := by
  exact IsZero.of_epi (cokernel.π _) (IsZero.of_mono (L.Z p q).arrow h)

private theorem weak_at_zero (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (p q : ℤ)
    (hP : IsZero (X.pageInfinity L p q))
    (hG : IsZero ((X.imageFiltration (p + q) (A (p + q))).gradedPiece p)) :
    Epi (X.toPageInfinity L p q) ∧ Epi (X.toGradedPiece A p q) ∧
      kernelSubobject (X.toPageInfinity L p q) =
        kernelSubobject (X.toGradedPiece A p q) := by
  refine ⟨hP.epi _, hG.epi _, ?_⟩
  rw [hP.eq_zero_of_tgt (X.toPageInfinity L p q),
    hG.eq_zero_of_tgt (X.toGradedPiece A p q), kernelSubobject_zero, kernelSubobject_zero]

private theorem pageD_zero (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (r : ℕ) (p q : ℤ) (h : q - (r : ℤ) < a) :
    IsZero ((X.pageCouple r).D p q) := by
  obtain ⟨α, I, _, _, _, _, hmono, himage, _, _⟩ := pageCouple_image X
  have := hmono r p q
  have him : imageSubobject (I r p q) = ⊥ := by
    rw [himage r p q, (hD (p + r) (q - r) h).eq_zero_of_src (α r p q),
      imageSubobject_zero]
  have hz : I r p q = 0 := by
    apply Subobject.mk_eq_bot_iff_zero.mp
    rwa [imageSubobject_mono] at him
  exact IsZero.of_mono_eq_zero (I r p q) hz

private theorem pullback_kernel {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    [HasKernels D] [HasPullbacks D] {S T U : D} (f : S ⟶ T) (g : T ⟶ U) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply kernelSubobject_factors
    have hw := (Subobject.isPullback f (kernelSubobject g)).w
    rw [← Category.assoc, ← hw, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  · apply Subobject.le_of_factors
    apply pullback_factors
    apply kernelSubobject_factors
    rw [Category.assoc, kernelSubobject_arrow_comp]

private theorem tower_stationary (X : BigradedExactCouple C 0)
    (T : CycleBoundaryTower X) (r : ℕ) (p q : ℤ)
    (hout : (X.pageCouple r).d p q = 0)
    (hin : (X.pageCouple r).dInto p q = 0) :
    T.Z (r + 1) p q = T.Z r p q ∧ T.B (r + 1) p q = T.B r p q := by
  constructor
  · rw [T.Z_succ, hout, kernelSubobject_zero,
      Subobject.pullback_top, Subobject.exists_iso_map, Subobject.map_top,
      Subobject.mk_arrow]
  · have hker : (Subobject.pullback (T.projection r p q)).obj ⊥ =
        kernelSubobject (T.projection r p q) := by
      have hid : kernelSubobject (𝟙 ((X.pageCouple r).E p q)) = ⊥ := by
        rw [← Subobject.mk_arrow (kernelSubobject (𝟙 ((X.pageCouple r).E p q)))]
        apply Subobject.mk_eq_bot_iff_zero.mpr
        simpa only [Category.comp_id] using
          kernelSubobject_arrow_comp (𝟙 ((X.pageCouple r).E p q))
      simpa only [hid, Category.comp_id] using
        pullback_kernel (T.projection r p q) (𝟙 _)
    rw [T.B_succ, hin, imageSubobject_zero, hker, T.projection_kernel,
      Subobject.exists_iso_map, Subobject.map_mk]
    simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]

private theorem quotient_comparison {S P : C} (B Z : Subobject S) (h : B ≤ Z)
    (π : (Z : C) ⟶ P) [Epi π]
    (hk : kernelSubobject π = Subobject.mk (Subobject.ofLE B Z h)) :
    ∃ e : cokernel (Subobject.ofLE B Z h) ≅ P,
      cokernel.π (Subobject.ofLE B Z h) ≫ e.hom = π := by
  let k := Subobject.ofLE B Z h
  have hz : k ≫ π = 0 := by
    apply (kernelSubobject_factors_iff π k).mp
    rw [hk]
    exact Subobject.mk_factors_self k
  have hw : kernel.ι π ≫ cokernel.π k = 0 := by
    have hfac : (Subobject.mk k).Factors (kernel.ι π) := by
      rw [← hk]
      exact kernelSubobject_factors π _ (kernel.condition π)
    obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff k _).mp hfac
    change t ≫ k = kernel.ι π at ht
    rw [← ht, Category.assoc, cokernel.condition, comp_zero]
  let e : cokernel k ≅ P :=
    { hom := cokernel.desc k π hz
      inv := Abelian.epiDesc π (cokernel.π k) hw
      hom_inv_id := by
        apply (cancel_epi (cokernel.π k)).mp
        simp
      inv_hom_id := by
        apply (cancel_epi π).mp
        simp }
  exact ⟨e, cokernel.π_desc k π hz⟩

private theorem stabilized_quotient_comparison {S P : C}
    (B Z B' Z' : Subobject S) (hB : B = B') (hZ : Z = Z')
    (h : B ≤ Z) (h' : B' ≤ Z') (hle : Z ≤ Z')
    (π : (Z' : C) ⟶ P) [Epi π]
    (hk : kernelSubobject π = Subobject.mk (Subobject.ofLE B' Z' h')) :
    ∃ e : cokernel (Subobject.ofLE B Z h) ≅ P,
      cokernel.π (Subobject.ofLE B Z h) ≫ e.hom = Subobject.ofLE Z Z' hle ≫ π := by
  subst B'
  subst Z'
  simpa only [Subobject.ofLE_refl, Category.id_comp] using quotient_comparison B Z h π hk

/-- For any limiting subobjects and normalized diagonal colimits, the two canonical
maps to the infinite page and the filtration graded piece are epimorphic with equal kernels.

Proof: fix `(p,q)`. Choose a page number `R` larger than both differential bounds
and with `u = p - R + 2 ≤ 0`, and put `v = q + R - 2`. The cycle/boundary recursion
is stationary from this page onwards, since the incoming source has negative first
index and the outgoing target has second index below `a`. Hence the greatest lower
bound of the cycles and least upper bound of the boundaries are those stationary
values; the infinite page is their quotient and canonically identifies with `E_R`.
Iterated derived-couple exactness identifies `D_R` with the incoming alpha images.
Along total degree `p+q`, the negative first-index transitions are invertible.
The normalization at first index zero and the cocone equations therefore identify
`D_R^{u,v}` with the image of `D^{p,q}` in the diagonal colimit, and the incoming
alpha image with the next filtration step. The next D term in the exact triangle
is the image of a map from `D^{p+R,q-R+1}` and vanishes by the D bound.
Thus the map from the first image to `E_R^{p,q}` is a cokernel of the next image.
The derived-g restriction equation, iterated R-2 times, identifies the composite
from `D^{p,q}` with the quotient of the original `g`. This is exactly the map
`toPageInfinity`, by the successor projection equation of the cycle tower.
The map `toGradedPiece` is the other cokernel of the same inclusion, precomposed
with the same epimorphism onto the image. Both maps are therefore epimorphic and
have the same kernel. For `p < 0`, the initial E term and all its subquotients
vanish; the two consecutive filtration steps are the whole colimit, so both
quotient targets are zero and the same assertion holds. This argument also
covers `q < a`, when the source D is zero.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011T and 012F.
(blueprint: lem-sp-half-plane-weak-convergence) -/
theorem halfPlane_weak_convergence (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (L : LimitSubobjects X) (A : ∀ n : ℤ, AlphaColimit X n)
    (hA : ∀ n : ℤ, (A n).obj = X.D 0 n)
    (hι : ∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
      eqToHom (by congr 1; omega)) : X.WeaklyConvergesTo L A := by
  intro p q
  have hgraded : Epi (X.toGradedPiece A p q) := by
    dsimp [toGradedPiece]
    infer_instance
  by_cases hqzero : q < a
  · have hG := IsZero.of_epi (X.toGradedPiece A p q) (hD p q hqzero)
    exact weak_at_zero X L A p q (infinity_zero X L p q (hE p q (Or.inr hqzero))) hG
  by_cases hpzero : p < 0
  · have htop (i : ℤ) (hi : i ≤ 0) :
        (X.imageFiltration (p + q) (A (p + q))).step i = ⊤ := by
      have := cocone_iso_left X a hE A hA hι (p + q) i hi
      change imageSubobject ((A (p + q)).ι i) = ⊤
      rw [imageSubobject_mono]
      exact Subobject.mk_eq_top_of_isIso _
    have hG := graded_zero_of_step_eq (X.imageFiltration (p + q) (A (p + q))) p
      ((htop (p + 1) (by omega)).trans (htop p (by omega)).symm)
    exact weak_at_zero X L A p q (infinity_zero X L p q (hE p q (Or.inl hpzero))) hG
  let r : ℕ := (max p (q - a) + 1).toNat
  have hp : p ≤ (r : ℤ) := by dsimp [r]; omega
  have hq : q - a < (r : ℤ) := by dsimp [r]; omega
  let T := X.cycleBoundaryTower
  have hs (t : ℕ) (ht : r ≤ t) :
      T.Z (t + 1) p q = T.Z t p q ∧ T.B (t + 1) p q = T.B t p q := by
    apply tower_stationary X T
    · exact (page_zero X _ _ (hE _ _ (Or.inr (by omega))) t).eq_zero_of_tgt _
    · exact (page_zero X _ _ (hE _ _ (Or.inl (by omega))) t).eq_zero_of_src _
  have htail (t : ℕ) (ht : r ≤ t) :
      T.Z t p q = T.Z r p q ∧ T.B t p q = T.B r p q := by
    induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ t ht ih => exact ⟨(hs t ht).1.trans ih.1, (hs t ht).2.trans ih.2⟩
  have hZ : L.Z p q = T.Z r p q := by
    apply le_antisymm ((L.Z_glb p q).1 ⟨r, rfl⟩)
    apply (L.Z_glb p q).2
    rintro _ ⟨t, rfl⟩
    by_cases ht : r ≤ t
    · exact le_of_eq (htail t ht).1.symm
    · exact antitone_nat_of_succ_le (f := fun s ↦ T.Z s p q)
        (fun s ↦ T.Z_decreasing s p q) (by omega)
  have hB : L.B p q = T.B r p q := by
    apply le_antisymm
    · apply (L.B_lub p q).2
      rintro _ ⟨t, rfl⟩
      by_cases ht : r ≤ t
      · exact le_of_eq (htail t ht).2
      · exact monotone_nat_of_le_succ (f := fun s ↦ T.B s p q)
          (fun s ↦ T.B_increasing s p q) (by omega)
    · exact (L.B_lub p q).1 ⟨r, rfl⟩
  have hle : L.Z p q ≤ T.Z r p q := (L.Z_glb p q).1 ⟨r, rfl⟩
  have hg : (T.Z r p q).Factors (X.initialG p q) :=
    Subobject.factors_of_le _ hle (g_factors_limitCycles X L p q)
  have hproj : Epi (T.projection r p q) := T.projection_epi r p q
  let := hproj
  have hc : ∃ e : X.pageInfinity L p q ≅ (X.pageCouple r).E p q,
      cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
        (limitBoundary_le_cycle X L p q)) ≫ e.hom =
      Subobject.ofLE (L.Z p q) (T.Z r p q) hle ≫ T.projection r p q := by
    exact stabilized_quotient_comparison (L.B p q) (L.Z p q) (T.B r p q) (T.Z r p q)
      hB hZ (limitBoundary_le_cycle X L p q) (T.B_le_Z r p q) hle
      (T.projection r p q) (T.projection_kernel r p q)
  obtain ⟨e, he⟩ := hc
  obtain ⟨f, hf⟩ := finitePage_image_quotient X (fun i j hi ↦ hE i j (Or.inl hi)) A hA hι r p q hp
    (pageD_zero X a hD r (p + 2) (q - 1) (by omega)) hg
  have hlift : (L.Z p q).factorThru (X.initialG p q)
      (g_factors_limitCycles X L p q) ≫ Subobject.ofLE _ _ hle =
      (T.Z r p q).factorThru (X.initialG p q) hg := by
    apply (cancel_mono (T.Z r p q).arrow).mp
    simp
  have hcomm : X.toPageInfinity L p q ≫ (e ≪≫ f).hom = X.toGradedPiece A p q := by
    rw [Iso.trans_hom, ← Category.assoc]
    change (((L.Z p q).factorThru (X.initialG p q)
      (g_factors_limitCycles X L p q) ≫
      cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
        (limitBoundary_le_cycle X L p q))) ≫ e.hom) ≫ f.hom = _
    rw [Category.assoc _ _ e.hom, he, ← Category.assoc, hlift, Category.assoc]
    exact hf
  let := hgraded
  have hpage : Epi (X.toPageInfinity L p q) := by
    have hfac : X.toPageInfinity L p q = X.toGradedPiece A p q ≫ (e ≪≫ f).inv := by
      rw [← hcomm]
      simp
    rw [hfac]
    infer_instance
  refine ⟨hpage, hgraded, ?_⟩
  simpa only [hcomm] using
    (kernelSubobject_comp_mono (X.toPageInfinity L p q) (e ≪≫ f).hom).symm

end CategoryTheory.BigradedExactCouple
