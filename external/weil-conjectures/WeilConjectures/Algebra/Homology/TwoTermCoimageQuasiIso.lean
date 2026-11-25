/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Cohomology projection of a two-term coimage complex

Source: Stacks Project, Tags 010V, 0118, and 08J5.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A two-term complex consisting of the coimage of the incoming differential
and the cycles maps quasi-isomorphically to the single cohomology object.
Source: Stacks Project, [Section 010V](https://stacks.math.columbia.edu/tag/010V),
[Tag 0118](https://stacks.math.columbia.edu/tag/0118), and
[Remark 08J5](https://stacks.math.columbia.edu/tag/08J5)
(blueprint: lem-weil-pbc-two-term-coimage-quasiiso).

Proof: away from `q - 1` and `q`, the source has a zero term, hence zero
cohomology. At `q - 1`, its outgoing differential is mono and its incoming
term is zero, so its cohomology is zero. The single complex has zero
cohomology in all these degrees too, and any map between zero objects is
an isomorphism. At `q`, the outgoing term is zero. Identify its cycles with
`M.X q`, and then with `K.cycles q` using `e₁`. Under this identification the
image of the incoming differential is the image of `K.toCycles (q - 1) q`:
by `hd`, the composites into `K.X q` agree after precomposing with the epi
`cokernel.π (kernel.ι (K.d (q - 1) q))` and the isomorphism `e₀.inv`;
cancel the mono cycles inclusion to get equality of these corestrictions.
Precomposition with an epi preserves the image. Thus the source cohomology
is the cokernel of the boundaries inclusion into `K.cycles q`, namely
`K.homology q`. The equation `hb` says the induced map on that cokernel is
the identity, after the canonical identification of the target single-complex
cohomology with `K.homology q`. It is therefore an isomorphism in every degree.
For the zero complex or a zero incoming differential the same calculation
has zero coimage and reduces to the identity on cycles; there is no boundedness
hypothesis on `K` and no positivity hypothesis on `q`.
-/
theorem twoTermCoimage_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (K M : CochainComplex C ℤ) (q : ℤ)
    (hM : ∀ r : ℤ, r ≠ q - 1 → r ≠ q → IsZero (M.X r))
    (e₀ : M.X (q - 1) ≅ cokernel (kernel.ι (K.d (q - 1) q)))
    (e₁ : M.X q ≅ K.cycles q)
    (hd : cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
      M.d (q - 1) q ≫ e₁.hom ≫ K.iCycles q = K.d (q - 1) q)
    (hm : Mono (M.d (q - 1) q))
    (b : M ⟶ (singleFunctor C q).obj (K.homology q))
    (hb : e₁.inv ≫ b.f q ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
      K.homologyπ q) : QuasiIso b := by
  have hprev : (ComplexShape.up ℤ).prev q = q - 1 := by simp
  have hnext : (ComplexShape.up ℤ).next q = q + 1 := by simp
  let L := (singleFunctor C q).obj (K.homology q)
  have hL (r : ℤ) (hr : r ≠ q) : IsZero (L.X r) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q
      (K.homology q) r hr
  have hdM : M.d q (q + 1) = 0 :=
    (hM (q + 1) (by omega) (by omega)).eq_of_tgt _ _
  have hw : M.d (q - 1) q ≫ b.f q = 0 := by
    rw [← b.comm]
    rw [(hL (q - 1) (by omega)).eq_of_src (L.d (q - 1) q) 0]
    simp
  let S := ShortComplex.mk (M.d (q - 1) q) (b.f q) hw
  let T := ShortComplex.mk (K.toCycles (q - 1) q) (K.homologyπ q)
    (K.toCycles_comp_homologyπ (q - 1) q)
  have hT : T.Exact :=
    T.exact_of_g_is_cokernel (K.homologyIsCokernel (q - 1) q hprev)
  have hcore : cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
      M.d (q - 1) q ≫ e₁.hom = K.toCycles (q - 1) q := by
    apply (cancel_mono (K.iCycles q)).1
    simpa only [Category.assoc, K.toCycles_i] using hd
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)
  let φ : T ⟶ S :=
    { τ₁ := cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv
      τ₂ := e₁.inv
      τ₃ := e.inv
      comm₁₂ := by
        dsimp [T, S]
        rw [← hcore]
        simp
      comm₂₃ := by
        dsimp [T, S]
        rw [← hb]
        simp [e] }
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hT
  have : Epi (b.f q) := by
    have : Epi (e₁.inv ≫ b.f q ≫ e.hom) := by
      change Epi (e₁.inv ≫ b.f q ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom)
      rw [hb]
      infer_instance
    have : Epi (e₁.inv ≫ b.f q) :=
      (epi_comp_iff_of_isIso (e₁.inv ≫ b.f q) e.hom).1 (by
        simpa only [Category.assoc] using this)
    exact epi_of_epi e₁.inv (b.f q)
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = q
  · subst i
    rw [quasiIsoAt_iff' b (q - 1) q (q + 1) hprev hnext]
    apply (ShortComplex.quasiIso_iff_of_zeros' _ hdM
      ((hL (q - 1) (by omega)).eq_of_src _ _)
      ((hL (q + 1) (by omega)).eq_of_tgt _ _)).2
    exact ⟨hS, show Epi (b.f q) from inferInstance⟩
  · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
    rw [quasiIsoAt_iff_exactAt' b i hLex]
    by_cases hi' : i = q - 1
    · subst i
      rw [HomologicalComplex.exactAt_iff' M (q - 2) (q - 1) q (by simp; omega)
        (by simp)]
      apply (ShortComplex.exact_iff_mono _
        ((hM (q - 2) (by omega) (by omega)).eq_of_src _ _)).2
      exact hm
    · exact HomologicalComplex.ExactAt.of_isZero (hM i hi' hi)

end CochainComplex
