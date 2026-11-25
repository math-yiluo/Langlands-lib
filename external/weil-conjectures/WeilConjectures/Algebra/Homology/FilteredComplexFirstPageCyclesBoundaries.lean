/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject

/-! # The first-page cycles and boundaries of a filtered complex

Source: Stacks Project, Homology, Tag 012K
(blueprint: lem-sp-filtered-complex-first-page-cycles-boundaries).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

private theorem pullback_inf {A B : C} (f : A ⟶ B) (S T : Subobject B) :
    (Subobject.pullback f).obj (S ⊓ T) =
      (Subobject.pullback f).obj S ⊓ (Subobject.pullback f).obj T :=
  (Subobject.gc_exists_pullback f).u_inf

private theorem pullback_kernel_of_eq {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (k : A ⟶ D) (hk : f ≫ g = k) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject k := by
  subst k
  apply le_antisymm
  · apply le_kernelSubobject
    have hf := (Subobject.factors_pullback_obj_iff f (kernelSubobject g) _).mp
      ((Subobject.le_iff_factors_arrow _ _).mp le_rfl)
    simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp hf
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
    apply kernelSubobject_factors
    simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)

private theorem exists_image {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    (Subobject.«exists» g).obj (imageSubobject f) = imageSubobject (f ≫ g) := by
  rw [Subobject.exists_obj_eq_imageSubobject,
    ← imageSubobject_comp_of_epi (factorThruImageSubobject f),
    ← Category.assoc, imageSubobject_arrow_comp]

private theorem step_mono (F : DecreasingFiltration K) (p n : ℤ) :
    Mono ((F.step p).arrow.f n) := by
  change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step p).arrow)
  infer_instance

private theorem quotient_epi (F : DecreasingFiltration K) (p n : ℤ) :
    Epi ((F.complexQuotientπ p (p + 1) (by omega)).f n) := by
  change Epi ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
    (cokernel.π (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega)))))
  infer_instance

private theorem quotient_kernel (F : DecreasingFiltration K) (p n : ℤ) :
    kernelSubobject ((F.complexQuotientπ p (p + 1) (by omega)).f n) =
      imageSubobject ((Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega))).f n) := by
  let l := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have h := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk l (cokernel.π l) (cokernel.condition l))
    (cokernelIsCokernel l)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
  exact ((ShortComplex.exact_iff_image_eq_kernel _).mp h).symm

private theorem step_le (F : DecreasingFiltration K) {p q : ℤ} (h : p ≤ q)
    (n : ℤ) : F.complexStep q n ≤ F.complexStep p n := by
  let l := Subobject.ofLE (F.step q) (F.step p) (F.antitone_step h)
  have hl : l.f n ≫ (F.step p).arrow.f n = (F.step q).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow (F.antitone_step h))
  dsimp only [complexStep]
  simpa only [hl] using (imageSubobject_comp_le (l.f n) ((F.step p).arrow.f n))

private theorem step_image_d (F : DecreasingFiltration K) (p a b : ℤ) :
    (Subobject.«exists» (K.d a b)).obj (F.complexStep p a) =
      (Subobject.«exists» ((F.step p).arrow.f b)).obj
        (imageSubobject ((F.step p : CochainComplex C ℤ).d a b)) := by
  dsimp only [complexStep]
  rw [exists_image, exists_image, (F.step p).arrow.comm]

private theorem step_d_le (F : DecreasingFiltration K) (p a b : ℤ) :
    F.complexStep p a ≤ (Subobject.pullback (K.d a b)).obj (F.complexStep p b) := by
  apply (Subobject.gc_exists_pullback _ _ _).mp
  rw [step_image_d, Subobject.exists_obj_eq_imageSubobject]
  exact (imageSubobject_comp_le _ _)

private theorem step_pullback_next (F : DecreasingFiltration K) (p n : ℤ) :
    (Subobject.pullback ((F.step p).arrow.f n)).obj (F.complexStep (p + 1) n) =
      imageSubobject ((Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega))).f n) := by
  have := step_mono F p n
  let l := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have hl : l.f n ≫ (F.step p).arrow.f n = (F.step (p + 1)).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow (F.antitone_step (show p ≤ p + 1 by omega)))
  dsimp only [complexStep]
  simp only [← hl]
  rw [← exists_image, Subobject.exists_iso_map ((F.step p).arrow.f n),
    Subobject.pullback_map_self]

private theorem step_next_image (F : DecreasingFiltration K) (p n : ℤ) :
    F.complexStep (p + 1) n =
      (Subobject.«exists» ((F.step p).arrow.f n)).obj
        (imageSubobject ((Subobject.ofLE (F.step (p + 1)) (F.step p)
          (F.antitone_step (by omega))).f n)) := by
  let l := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have hl : l.f n ≫ (F.step p).arrow.f n = (F.step (p + 1)).arrow.f n :=
    congrArg (fun f => f.f n)
      (Subobject.ofLE_arrow (F.antitone_step (show p ≤ p + 1 by omega)))
  dsimp only [complexStep]
  rw [exists_image, hl]

/-- The page-one cycle and boundary formulas.
Source: Stacks Project, Tag 012K, displayed formulas and Lemma 12.24.2.
(blueprint: lem-sp-filtered-complex-first-page-cycles-boundaries)

Proof: Write m_n for the inclusion F^pK^n → K^n, l_n for the inclusion
F^{p+1}K^n → F^pK^n and q_n for the graded projection. Evaluation of the cokernel
sequence of complexes is a cokernel sequence, so q_n is epic and its kernel is
image l_n. The graded differential δ satisfies q_n ≫ δ = d_p ≫ q_{n+1}, where d_p
is the differential restricted to F^p. Pulling back ker δ along q_n therefore gives
the inverse image under d_p of image l_{n+1}. Under the mono m_n this is precisely
F^pK^n ∩ d⁻¹(F^{p+1}K^{n+1}). It contains F^{p+1}K^n since the steps are subcomplexes,
so the extra sum in complexCycles is redundant. The image under an epimorphism of
the pullback of a subobject is that subobject. Applying this to ker δ proves the
cycle formula.
For boundaries, q_{n-1} is epic, hence image δ = image(q_{n-1} ≫ δ) =
image(d_p ≫ q_n). Under m_n, image d_p is d(F^pK^{n-1}), which is contained in
F^pK^n by the subcomplex condition; thus the intersection in complexBoundaries at
r=1 is redundant. Pullback along the mono m_n recovers image d_p. Adding the
subobject F^{p+1} before applying q_n has no effect on its image, since q_n kills
that subobject. The resulting image is exactly image(d_p ≫ q_n) = image δ. -/
theorem filteredComplex_firstPage_cycles_boundaries (F : DecreasingFiltration K) :
    ∀ p n : ℤ,
      F.complexCycles p n 1 = kernelSubobject ((F.gradedPiece p).d n (n + 1)) ∧
      F.complexBoundaries p n 1 = imageSubobject ((F.gradedPiece p).d (n - 1) n) := by
  intro p n
  have := step_mono F p n
  have := step_mono F p (n + 1)
  have := quotient_epi F p n
  let q := F.complexQuotientπ p (p + 1) (by omega)
  constructor
  · have hsum : F.complexStep (p + 1) n ≤
        F.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj
          (F.complexStep (p + 1) (n + 1)) :=
      le_inf (step_le F (by omega) n) (step_d_le F (p + 1) n (n + 1))
    unfold complexCycles
    rw [sup_eq_left.mpr hsum, pullback_inf]
    have hself : (Subobject.pullback ((F.step p).arrow.f n)).obj
        (F.complexStep p n) = ⊤ := by
      rw [complexStep, imageSubobject_mono, Subobject.pullback_self]
    rw [hself, top_inf_eq, ← Subobject.pullback_comp]
    rw [(F.step p).arrow.comm, Subobject.pullback_comp, step_pullback_next,
      ← quotient_kernel, pullback_kernel_of_eq _ _ _ rfl]
    change (Subobject.«exists» (q.f n)).obj
      (kernelSubobject ((F.step p : CochainComplex C ℤ).d n (n + 1) ≫
        q.f (n + 1))) = _
    rw [← q.comm, ← pullback_kernel_of_eq _ _ _ rfl, Subobject.exists_obj_pullback_obj]
    rfl
  · have := quotient_epi F p (n - 1)
    have hp : p - 1 + 1 = p := by omega
    have hi : (Subobject.«exists» (K.d (n - 1) n)).obj
        (F.complexStep p (n - 1)) ≤ F.complexStep p n :=
      (Subobject.gc_exists_pullback _ _ _).mpr (step_d_le F p (n - 1) n)
    unfold complexBoundaries
    rw [hp, inf_eq_right.mpr hi, step_image_d, step_next_image,
      ← Subobject.exists_obj_sup ((F.step p).arrow.f n),
      Subobject.exists_iso_map ((F.step p).arrow.f n), Subobject.pullback_map_self,
      Subobject.exists_obj_sup, exists_image, exists_image]
    have hq : (Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega))).f n ≫ q.f n = 0 := by
      exact congrArg (fun f => f.f n) (cokernel.condition
        (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))))
    change imageSubobject ((F.step p : CochainComplex C ℤ).d (n - 1) n ≫ q.f n) ⊔
      imageSubobject _ = _
    rw [hq, imageSubobject_zero, sup_bot_eq, ← q.comm, imageSubobject_comp_of_epi]
    rfl

end CategoryTheory.DecreasingFiltration
