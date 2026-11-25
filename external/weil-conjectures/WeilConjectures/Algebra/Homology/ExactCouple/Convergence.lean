/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration
/-!
# Convergence of the spectral sequence of an exact couple

We consider exact couples indexed by `ℤ × ℤ` whose map `α` has degree `(-1, 0)` and whose map `g`
has degree `0`. We think of an index `(p, n)` as a filtration degree `p` and a total degree `n`:
the bigraded couples of the blueprint, indexed by `(p, q)` with `α` of degree `(-1, 1)`,
correspond to these through `(p, q) ↦ (p, p + q)`.

The abutment of such a couple is given by structure maps `ι p n : D^{p, n} ⟶ Aⁿ`. When the
objects `D^{p, n}` vanish for `p ≫ 0` and the maps `ι p n` are isomorphisms for `p ≪ 0`, the
abutment is filtered by the images `Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)`, and the spectral sequence of
the couple converges to this filtration: each entry `E_r^{p, n}` eventually has vanishing
incoming and outgoing differentials, and is then identified with the graded piece `grᵖ Aⁿ`,
compatibly with the maps `ι` (`CategoryTheory.ExactCouple.abutmentConvergenceData`).

## Main definitions

- `CategoryTheory.ExactCouple.IsRegular`, `CategoryTheory.ExactCouple.IsComplete`: regular and
  complete couples.
- `CategoryTheory.ExactCouple.ConvergenceData`, `CategoryTheory.ExactCouple.ConvergesTo`:
  convergence of the spectral sequence of a couple to a filtration of its abutment.
- `CategoryTheory.ExactCouple.abutmentFiltration`: the filtration of the abutment by the images
  of the `D`-objects.
- `CategoryTheory.ExactCouple.abutmentConvergenceData`: the convergence data of a couple which is
  bounded in each total degree.

## Main statements

- `CategoryTheory.ExactCouple.convergesTo_abutmentFiltration`: convergence of the spectral
  sequence of a couple which is bounded in each total degree.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cokernel of the inclusion of two subobjects given by monomorphisms `u` and `v` is the
cokernel of a morphism `φ` with `φ ≫ v = u`. -/
noncomputable def cokernelOfLEIso {A U V : C} (u : U ⟶ A) (v : V ⟶ A) [Mono u] [Mono v]
    (φ : U ⟶ V) (hφ : φ ≫ v = u) {P Q : Subobject A} (hP : P = Subobject.mk u)
    (hQ : Q = Subobject.mk v) (h : P ≤ Q) :
    cokernel (Subobject.ofLE P Q h) ≅ cokernel φ :=
  cokernel.mapIso _ _ (Subobject.isoOfEqMk P u hP) (Subobject.isoOfEqMk Q v hQ)
    (by rw [← cancel_mono v]; simp [hφ])

@[reassoc (attr := simp)]
lemma π_cokernelOfLEIso_hom {A U V : C} (u : U ⟶ A) (v : V ⟶ A) [Mono u] [Mono v]
    (φ : U ⟶ V) (hφ : φ ≫ v = u) {P Q : Subobject A} (hP : P = Subobject.mk u)
    (hQ : Q = Subobject.mk v) (h : P ≤ Q) :
    cokernel.π _ ≫ (cokernelOfLEIso u v φ hφ hP hQ h).hom =
      (Subobject.isoOfEqMk Q v hQ).hom ≫ cokernel.π φ := by
  simp [cokernelOfLEIso]

namespace ExactCouple

/-- The degree of the map `g` of the `N`-th derived couple of a couple with `α` of degree
`(-1, 0)` and `g` of degree `0` is `(N, 0)`. -/
lemma degIter_neg_one_zero (N : ℕ) :
    degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ) N = ((N : ℤ), 0) := by
  rw [degIter_eq]
  ext <;> simp

variable {b : ℤ × ℤ} (X : ExactCouple C ((-1, 0) : ℤ × ℤ) b 0)

/-- A couple is *regular* if for every index `i`, the differentials `d_r` arriving at `i` vanish
for `r ≫ 0`; equivalently, the boundaries `B_r ⊆ E` at `i` are eventually constant.

(blueprint: `def-sp-convergence`) -/
def IsRegular : Prop :=
  ∀ i : ℤ × ℤ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ j, (X.derivedIter n).d j i = 0

/-- A couple is *complete* if for every index `i` the images of the composites
`αʳ : D (i + (r, 0)) ⟶ D i` have zero intersection.

(blueprint: `def-sp-convergence`) -/
def IsComplete : Prop :=
  ∀ (i : ℤ × ℤ) (P : Subobject (X.D i)),
    (∀ r : ℕ, P ≤ imageSubobject (X.αPow r (i + ((r : ℤ), 0)) i)) → P = ⊥

/-- The data of the convergence of the spectral sequence of the couple `X` to the filtrations
`F n` of objects `A n`, along the structure maps `ι p n : D^{p, n} ⟶ Aⁿ` of the abutment.

For every index `(p, n)` (filtration degree `p`, total degree `n`), it consists of a page
`stage p n` from which on the differentials leaving and arriving at `(p, n)` vanish (so that the
entry has reached its stable value `E_∞^{p, n}`), and of isomorphisms `E_N^{p, n} ≅ grᵖ Aⁿ` on
these pages, compatible with the structure maps: the composite of the map
`g : D_N^{p - N, n} ⟶ E_N^{p, n}` of the `N`-th derived couple with the isomorphism is induced by
`D_N^{p - N, n} ⊆ D^{p - N, n} ⟶ Aⁿ`, which factors through `Fᵖ Aⁿ`.

This is the convention for a couple whose map `g` has degree `0`.

(blueprint: `def-sp-convergence`) -/
structure ConvergenceData {A : ℤ → C} (ι : ∀ p n : ℤ, X.D (p, n) ⟶ A n)
    (F : ∀ n, DecreasingFiltration (A n)) where
  /-- The page from which on the entry at `(p, n)` is stable. -/
  stage (p n : ℤ) : ℕ
  d_out (p n : ℤ) (N : ℕ) (hN : stage p n ≤ N) (j : ℤ × ℤ) : (X.derivedIter N).d (p, n) j = 0
  d_in (p n : ℤ) (N : ℕ) (hN : stage p n ≤ N) (j : ℤ × ℤ) : (X.derivedIter N).d j (p, n) = 0
  /-- The identification of the stable entry `E_N^{p, n}` with the graded piece `grᵖ Aⁿ`. -/
  iso (p n : ℤ) (N : ℕ) (hN : stage p n ≤ N) : (X.derivedIter N).E (p, n) ≅ (F n).gr p
  comm (p n : ℤ) (N : ℕ) (hN : stage p n ≤ N) :
    ∃ φ : (X.derivedIter N).D (p - N, n) ⟶ ((F n).F p : C),
      φ ≫ ((F n).F p).arrow = X.ιIter N (p - N, n) ≫ ι (p - N) n ∧
      (X.derivedIter N).g (p - N, n) (p, n) ≫ (iso p n N hN).hom = φ ≫ cokernel.π _

/-- The spectral sequence of the couple *converges* to the filtrations `F n` of the objects
`A n`, along the structure maps `ι p n : D^{p, n} ⟶ Aⁿ` of the abutment, if it admits
convergence data `CategoryTheory.ExactCouple.ConvergenceData`.

(blueprint: `def-sp-convergence`) -/
def ConvergesTo {A : ℤ → C} (ι : ∀ p n : ℤ, X.D (p, n) ⟶ A n)
    (F : ∀ n, DecreasingFiltration (A n)) : Prop :=
  Nonempty (X.ConvergenceData ι F)

section Abutment

variable {A : ℤ → C} (ι : ∀ p n : ℤ, X.D (p, n) ⟶ A n)
  (hι : ∀ p n : ℤ, X.α (p + 1, n) (p, n) ≫ ι p n = ι (p + 1) n)

include hι in
lemma αPow_comp (N : ℕ) (p p' n : ℤ) (h : p' + N = p) :
    X.αPow N (p, n) (p', n) ≫ ι p' n = ι p n := by
  induction N generalizing p' with
  | zero =>
    obtain rfl : p' = p := by simpa using h
    simp [αPow]
  | succ N ih =>
    simp only [αPow, Category.assoc]
    rw [show ((p', n) : ℤ × ℤ) - ((-1, 0) : ℤ × ℤ) = (p' + 1, n) by ext <;> simp, hι,
      ih (p' + 1) (by push_cast at h; omega)]

include hι in
@[reassoc]
lemma derivedIter_α_ιIter_comp (N : ℕ) (p n : ℤ) :
    (X.derivedIter N).α (p + 1, n) (p, n) ≫ X.ιIter N (p, n) ≫ ι p n =
      X.ιIter N (p + 1, n) ≫ ι (p + 1) n := by
  rw [X.α_ιIter_assoc, hι]

/-- The filtration of the abutment `Aⁿ` by the images `Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)`. -/
noncomputable def abutmentFiltration (n : ℤ) : DecreasingFiltration (A n) where
  F p := imageSubobject (ι p n)
  F_succ_le p := by
    rw [← hι p n]
    exact imageSubobject_comp_le _ _

include hι in
lemma imageSubobject_ι_eq_mk (N : ℕ) (p p' n : ℤ) (h : p' + N = p) [IsIso (ι p' n)] :
    imageSubobject (ι p n) = Subobject.mk (X.ιIter N (p', n) ≫ ι p' n) := by
  obtain ⟨π, _, hπ⟩ := X.exists_epi_comp_ιIter N (p, n) (p', n)
    (by ext <;> simp; omega)
  rw [← X.αPow_comp ι hι N p p' n h, ← hπ, Category.assoc, imageSubobject_comp_eq_of_epi,
    imageSubobject_mono]

variable (hiso : ∀ n : ℤ, ∃ m : ℤ, ∀ p ≤ m, IsIso (ι p n))
  (hzero : ∀ n : ℤ, ∃ M : ℤ, ∀ p ≥ M, IsZero (X.D (p, n)))

/-- The page `N` from which on the entry at `(p, n)` of the spectral sequence of a bounded couple
is stable: `ι` is an isomorphism in filtration degrees `≤ p - N + 1`, and `D` vanishes in
filtration degrees `≥ p + b.1 + N` in total degree `n + b.2`. -/
noncomputable def abutmentStage (p n : ℤ) : ℕ :=
  (p - (hiso n).choose + 1).toNat + ((hzero (n + b.2)).choose - p - b.1).toNat

lemma exact_derivedIter_α_g (N : ℕ) (p n : ℤ) :
    (ShortComplex.mk _ _ ((X.derivedIter N).α_g (p - N + 1, n) (p - N, n) (p, n))).Exact :=
  (X.derivedIter N).exact_α_g _ _ _ (by ext <;> simp)
    (by rw [degIter_neg_one_zero]; ext <;> simp)

section Stable

variable {X ι hiso hzero} {p n : ℤ} {N : ℕ} (hN : X.abutmentStage ι hiso hzero p n ≤ N)
include hN

lemma isIso_ι_of_abutmentStage_le (p' : ℤ) (hp' : p' ≤ p - N + 1) : IsIso (ι p' n) :=
  (hiso n).choose_spec _ (by simp only [abutmentStage] at hN; omega)

lemma derivedIter_d_eq_zero_of_abutmentStage_le (j : ℤ × ℤ) :
    (X.derivedIter N).d (p, n) j = 0 := by
  obtain ⟨π, _, -⟩ := X.exists_epi_comp_ιIter N (p + b.1 + N, n + b.2) (p + b.1, n + b.2)
    (by ext <;> simp)
  have hu : IsZero ((X.derivedIter N).D (p + b.1, n + b.2)) :=
    IsZero.of_epi π ((hzero (n + b.2)).choose_spec _ (by simp only [abutmentStage] at hN; omega))
  rw [(X.derivedIter N).d_eq (p, n) (p + b.1, n + b.2) j rfl, hu.eq_of_tgt
    ((X.derivedIter N).f (p, n) (p + b.1, n + b.2)) 0, zero_comp]

include hι in
lemma derivedIter_d_eq_zero_of_abutmentStage_le' (j : ℤ × ℤ) :
    (X.derivedIter N).d j (p, n) = 0 := by
  by_cases h : j + b = (p - N, n)
  · have := X.isIso_ι_of_abutmentStage_le hN (p - N - 1) (by omega)
    have := X.isIso_ι_of_abutmentStage_le hN (p - N) (by omega)
    have : Mono ((X.derivedIter N).α (p - N, n) (p - N - 1, n)) := by
      have := X.derivedIter_α_ιIter_comp ι hι N (p - N - 1) n
      rw [sub_add_cancel] at this
      exact mono_of_mono_fac this
    have hf : (X.derivedIter N).f j (p - N, n) = 0 := by
      rw [← cancel_mono ((X.derivedIter N).α (p - N, n) (p - N - 1, n)), zero_comp]
      exact (X.derivedIter N).f_α _ _ _
    rw [(X.derivedIter N).d_eq j (p - N, n) _ h, hf, zero_comp]
  · rw [(X.derivedIter N).d_eq j (j + b) _ rfl, (X.derivedIter N).shape_g, comp_zero]
    intro h'
    apply h
    rw [degIter_neg_one_zero] at h'
    ext
    · have := congrArg _root_.Prod.fst h'
      simp at this
      simp
      omega
    · have := congrArg _root_.Prod.snd h'
      simp at this
      simpa using this

lemma epi_derivedIter_g_of_abutmentStage_le :
    Epi ((X.derivedIter N).g (p - N, n) (p, n)) := by
  refine ((X.derivedIter N).exact_g_f (p - N, n) (p, n) (p + b.1, n + b.2)
    (by rw [degIter_neg_one_zero]; ext <;> simp) (by ext <;> simp)).epi_f ?_
  obtain ⟨π, _, -⟩ := X.exists_epi_comp_ιIter N (p + b.1 + N, n + b.2) (p + b.1, n + b.2)
    (by ext <;> simp)
  exact (IsZero.of_epi π ((hzero (n + b.2)).choose_spec _
    (by simp only [abutmentStage] at hN; omega))).eq_of_tgt _ _

end Stable

/-- The identification `E_N^{p, n} ≅ grᵖ Aⁿ` of a stable entry of the spectral sequence of a
couple which is bounded in each total degree: both are the cokernel of
`α : D_N^{p - N + 1, n} ⟶ D_N^{p - N, n}`. -/
noncomputable def abutmentIso (p n : ℤ) (N : ℕ) (hN : X.abutmentStage ι hiso hzero p n ≤ N) :
    (X.derivedIter N).E (p, n) ≅ (X.abutmentFiltration ι hι n).gr p :=
  have := isIso_ι_of_abutmentStage_le hN (p - N) (by omega)
  have := isIso_ι_of_abutmentStage_le hN (p - N + 1) (by omega)
  have := epi_derivedIter_g_of_abutmentStage_le hN
  (X.exact_derivedIter_α_g N p n).gIsCokernel.coconePointUniqueUpToIso
      (colimit.isColimit _) ≪≫
    (cokernelOfLEIso (X.ιIter N (p - N + 1, n) ≫ ι (p - N + 1) n)
      (X.ιIter N (p - N, n) ≫ ι (p - N) n) ((X.derivedIter N).α (p - N + 1, n) (p - N, n))
      (X.derivedIter_α_ιIter_comp ι hι N (p - N) n)
      (P := (X.abutmentFiltration ι hι n).F (p + 1)) (Q := (X.abutmentFiltration ι hι n).F p)
      (X.imageSubobject_ι_eq_mk ι hι N (p + 1) (p - N + 1) n (by omega))
      (X.imageSubobject_ι_eq_mk ι hι N p (p - N) n (by omega))
      ((X.abutmentFiltration ι hι n).F_succ_le p)).symm

lemma abutmentIso_comm (p n : ℤ) (N : ℕ) (hN : X.abutmentStage ι hiso hzero p n ≤ N) :
    ∃ φ : (X.derivedIter N).D (p - N, n) ⟶ ((X.abutmentFiltration ι hι n).F p : C),
      φ ≫ ((X.abutmentFiltration ι hι n).F p).arrow = X.ιIter N (p - N, n) ≫ ι (p - N) n ∧
      (X.derivedIter N).g (p - N, n) (p, n) ≫ (X.abutmentIso ι hι hiso hzero p n N hN).hom =
        φ ≫ cokernel.π _ := by
  have := isIso_ι_of_abutmentStage_le hN (p - N) (by omega)
  have := isIso_ι_of_abutmentStage_le hN (p - N + 1) (by omega)
  let e := Subobject.isoOfEqMk ((X.abutmentFiltration ι hι n).F p) _
    (X.imageSubobject_ι_eq_mk ι hι N p (p - N) n (by omega))
  have := epi_derivedIter_g_of_abutmentStage_le hN
  refine ⟨e.inv, Subobject.ofMkLE_arrow _, ?_⟩
  have h₁ := (X.exact_derivedIter_α_g N p n).gIsCokernel.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) WalkingParallelPair.one
  dsimp only [abutmentIso]
  erw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h₁]
  refine (Iso.comp_inv_eq _).2 ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  erw [π_cokernelOfLEIso_hom]
  simp only [e, Iso.inv_hom_id_assoc]
  rfl

/-- **Convergence of the spectral sequence of a bounded exact couple.** Let `X` be an exact
couple indexed by `ℤ × ℤ` with `α` of degree `(-1, 0)` and `g` of degree `0`, and let
`ι : D^{p, n} ⟶ Aⁿ` be compatible with `α`. Suppose that in each total degree `n`, the maps
`ι` are isomorphisms for `p ≪ 0` and the objects `D^{p, n}` vanish for `p ≫ 0`. Then the
spectral sequence of `X` converges to the filtration `Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)`: these are its
convergence data.

(blueprint: `def-sp-convergence`) -/
noncomputable def abutmentConvergenceData :
    X.ConvergenceData ι (X.abutmentFiltration ι hι) where
  stage := X.abutmentStage ι hiso hzero
  d_out _ _ _ hN := derivedIter_d_eq_zero_of_abutmentStage_le hN
  d_in _ _ _ hN := derivedIter_d_eq_zero_of_abutmentStage_le' hι hN
  iso := X.abutmentIso ι hι hiso hzero
  comm := X.abutmentIso_comm ι hι hiso hzero

include hiso hzero in
/-- **Convergence of the spectral sequence of a bounded exact couple.** Let `X` be an exact
couple indexed by `ℤ × ℤ` with `α` of degree `(-1, 0)` and `g` of degree `0`, and let
`ι : D^{p, n} ⟶ Aⁿ` be compatible with `α`. Suppose that in each total degree `n`, the maps
`ι` are isomorphisms for `p ≪ 0` and the objects `D^{p, n}` vanish for `p ≫ 0`. Then the
spectral sequence of `X` converges to the filtration `Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)`.

(blueprint: `def-sp-convergence`) -/
theorem convergesTo_abutmentFiltration :
    X.ConvergesTo ι (X.abutmentFiltration ι hι) :=
  ⟨X.abutmentConvergenceData ι hι hiso hzero⟩

end Abutment

end ExactCouple

end CategoryTheory
