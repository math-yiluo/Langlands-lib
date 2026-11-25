/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.Algebra.Homology.ExactCouple.Convergence

/-!
# The spectral sequence of a filtered complex

Let `K` be a cochain complex in an abelian category with a decreasing filtration `F` by
subcomplexes (a `CategoryTheory.DecreasingFiltration` of `K` in the abelian category of cochain
complexes). The long exact cohomology sequences of the short exact sequences
`0 ⟶ Fᵖ⁺¹ K ⟶ Fᵖ K ⟶ grᵖ K ⟶ 0` form an exact couple with
`D^{p, n} = Hⁿ(Fᵖ K)` and `E^{p, n} = Hⁿ(grᵖ K)` (indexed by the filtration degree `p` and the
total degree `n`), whose spectral sequence starts with `E₁^{p, n} = Hⁿ(grᵖ K)`. When the
filtration is bounded in each degree, it converges to the cohomology of `K` with the image
filtration `Fᵖ Hⁿ(K) = im (Hⁿ(Fᵖ K) ⟶ Hⁿ(K))`.

## Main definitions

- `CategoryTheory.DecreasingFiltration.exactCouple`: the exact couple of a filtered complex.

## Main statements

- `CategoryTheory.DecreasingFiltration.convergesTo_exactCouple`: convergence of the spectral
  sequence of a filtered complex whose filtration is bounded in each degree.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma ShortComplex.exact_mk_of_eq {X₁ X₂ X₃ : C} {f f' : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃}
    (w : f ≫ g = 0) (w' : f' ≫ g' = 0) (hf : f = f') (hg : g = g')
    (h : (ShortComplex.mk f' g' w').Exact) : (ShortComplex.mk f g w).Exact := by
  subst hf hg
  exact h

namespace DecreasingFiltration

variable {K : CochainComplex C ℤ} (F : DecreasingFiltration K)

/-- The subcomplex `Fᵖ K`. -/
noncomputable abbrev piece (p : ℤ) : CochainComplex C ℤ :=
  Subobject.underlying.obj (F.F p)

/-- The short exact sequence `0 ⟶ Fᵖ⁺¹ K ⟶ Fᵖ K ⟶ grᵖ K ⟶ 0`. -/
noncomputable def ses (p : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (Subobject.ofLE _ _ (F.F_succ_le p)) (cokernel.π _) (cokernel.condition _)

lemma ses_shortExact (p : ℤ) : (F.ses p).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) (by dsimp [ses]; infer_instance)
    (by dsimp [ses]; infer_instance)

/-- The maps `α : Hⁿ(Fᵖ K) ⟶ Hⁿ(Fᵖ⁻¹ K)` of the exact couple of a filtered complex, induced by
the inclusions of subcomplexes. -/
noncomputable def coupleα (i j : ℤ × ℤ) : (F.piece i.1).homology i.2 ⟶ (F.piece j.1).homology j.2 :=
  if h : j.1 + 1 = i.1 ∧ i.2 = j.2 then
    HomologicalComplex.homologyMap (Subobject.ofLE (F.F i.1) (F.F j.1) (F.antitone (by omega)))
      i.2 ≫
      eqToHom (by rw [h.2])
  else 0

/-- The maps `f : Hⁿ(grᵖ K) ⟶ Hⁿ⁺¹(Fᵖ⁺¹ K)` of the exact couple of a filtered complex: the
connecting homomorphisms. -/
noncomputable def couplef (i j : ℤ × ℤ) : (F.gr i.1).homology i.2 ⟶ (F.piece j.1).homology j.2 :=
  if h : i.1 + 1 = j.1 ∧ i.2 + 1 = j.2 then
    (F.ses_shortExact i.1).δ i.2 j.2 (by simp [h.2]) ≫ eqToHom (by rw [← h.1]; rfl)
  else 0

/-- The maps `g : Hⁿ(Fᵖ K) ⟶ Hⁿ(grᵖ K)` of the exact couple of a filtered complex, induced by
the projections. -/
noncomputable def coupleg (i j : ℤ × ℤ) : (F.piece i.1).homology i.2 ⟶ (F.gr j.1).homology j.2 :=
  if h : i = j then
    HomologicalComplex.homologyMap (cokernel.π (Subobject.ofLE (F.F (i.1 + 1)) (F.F i.1)
      (F.F_succ_le _))) i.2 ≫ eqToHom (by rw [h]; rfl)
  else 0

lemma coupleα_self (p n : ℤ) :
    F.coupleα (p + 1, n) (p, n) =
      HomologicalComplex.homologyMap (Subobject.ofLE _ _ (F.F_succ_le p)) n := by
  rw [coupleα, dite_eq_left ⟨rfl, rfl⟩, eqToHom_refl, Category.comp_id]

lemma couplef_self (p n : ℤ) :
    F.couplef (p, n) (p + 1, n + 1) = (F.ses_shortExact p).δ n (n + 1) rfl := by
  rw [couplef, dite_eq_left ⟨rfl, rfl⟩, eqToHom_refl, Category.comp_id]

lemma coupleg_self (p n : ℤ) :
    F.coupleg (p, n) (p, n) = HomologicalComplex.homologyMap (cokernel.π _) n := by
  rw [coupleg, dite_eq_left rfl, eqToHom_refl, Category.comp_id]

lemma coupleα_eq_zero (i j : ℤ × ℤ) (h : i + ((-1, 0) : ℤ × ℤ) ≠ j) : F.coupleα i j = 0 := by
  rw [coupleα, dite_eq_right]
  rintro ⟨h₁, h₂⟩
  exact h (Prod.ext (by simp; omega) (by simp [h₂]))

lemma couplef_eq_zero (i j : ℤ × ℤ) (h : i + ((1, 1) : ℤ × ℤ) ≠ j) : F.couplef i j = 0 := by
  rw [couplef, dite_eq_right]
  rintro ⟨h₁, h₂⟩
  exact h (Prod.ext (by simp; omega) (by simp; omega))

lemma coupleg_eq_zero (i j : ℤ × ℤ) (h : i + 0 ≠ j) : F.coupleg i j = 0 := by
  rw [coupleg, dite_eq_right]
  rintro rfl
  exact h (add_zero _)

/-- Reduce statements about the maps of the couple to the case of the standard indices. -/
private lemma eq_of_add (i j : ℤ × ℤ) (a : ℤ × ℤ) (h : i + a = j) : j = (i.1 + a.1, i.2 + a.2) :=
  h.symm


lemma coupleα_coupleg (i j k : ℤ × ℤ) : F.coupleα i j ≫ F.coupleg j k = 0 := by
  by_cases hij : i + ((-1, 0) : ℤ × ℤ) = j
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨p, n⟩ := j
      obtain rfl : i = (p + 1, n) := by
        rw [Prod.ext_iff] at hij ⊢; simp at hij; omega
      rw [coupleα_self, coupleg_self, ← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero]
    · rw [F.coupleg_eq_zero j k (by simpa using hjk), comp_zero]
  · rw [F.coupleα_eq_zero i j hij, zero_comp]

lemma coupleg_couplef (i j k : ℤ × ℤ) : F.coupleg i j ≫ F.couplef j k = 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hjk : i + ((1, 1) : ℤ × ℤ) = k
    · obtain ⟨p, n⟩ := i
      obtain rfl : k = (p + 1, n + 1) := hjk.symm
      rw [coupleg_self, couplef_self]
      exact (F.ses_shortExact p).comp_δ n (n + 1) rfl
    · rw [F.couplef_eq_zero _ k hjk, comp_zero]
  · rw [F.coupleg_eq_zero i j (by simpa using hij), zero_comp]

lemma couplef_coupleα (i j k : ℤ × ℤ) : F.couplef i j ≫ F.coupleα j k = 0 := by
  by_cases hij : i + ((1, 1) : ℤ × ℤ) = j
  · by_cases hjk : j + ((-1, 0) : ℤ × ℤ) = k
    · obtain ⟨p, n⟩ := i
      obtain rfl : j = (p + 1, n + 1) := hij.symm
      obtain rfl : k = (p, n + 1) := by
        rw [← hjk]; ext <;> simp
      rw [couplef_self, coupleα_self]
      exact (F.ses_shortExact p).δ_comp n (n + 1) rfl
    · rw [F.coupleα_eq_zero j k hjk, comp_zero]
  · rw [F.couplef_eq_zero i j hij, zero_comp]

/-- **The exact couple of a filtered complex.** For a cochain complex `K` with a decreasing
filtration `F` by subcomplexes, the long exact cohomology sequences of
`0 ⟶ Fᵖ⁺¹ K ⟶ Fᵖ K ⟶ grᵖ K ⟶ 0` form an exact couple with `D^{p, n} = Hⁿ(Fᵖ K)`,
`E^{p, n} = Hⁿ(grᵖ K)`, `α` induced by the inclusions (of degree `(-1, 0)`), `g` induced by the
projections (of degree `0`) and `f` the connecting homomorphisms (of degree `(1, 1)`).

(blueprint: `thm-sp-spectral-object-yields`) -/
noncomputable def exactCouple : ExactCouple C ((-1, 0) : ℤ × ℤ) (1, 1) 0 where
  D i := (F.piece i.1).homology i.2
  E i := (F.gr i.1).homology i.2
  α := F.coupleα
  f := F.couplef
  g := F.coupleg
  shape_α := F.coupleα_eq_zero
  shape_f := F.couplef_eq_zero
  shape_g := F.coupleg_eq_zero
  α_g := F.coupleα_coupleg
  g_f := F.coupleg_couplef
  f_α := F.couplef_coupleα
  exact_α_g i j k hij hjk := by
    obtain ⟨p, n⟩ := j
    obtain rfl : k = (p, n) := by simpa using hjk.symm
    obtain rfl : i = (p + 1, n) := by
      rw [Prod.ext_iff] at hij ⊢; simp at hij; omega
    exact ShortComplex.exact_mk_of_eq _ _ (F.coupleα_self p n) (F.coupleg_self p n)
      ((F.ses_shortExact p).homology_exact₂ n)
  exact_g_f i j k hij hjk := by
    obtain rfl : j = i := by simpa using hij.symm
    obtain ⟨p, n⟩ := j
    obtain rfl : k = (p + 1, n + 1) := hjk.symm
    exact ShortComplex.exact_mk_of_eq _ _ (F.coupleg_self p n) (F.couplef_self p n)
      ((F.ses_shortExact p).homology_exact₃ n (n + 1) rfl)
  exact_f_α i j k hij hjk := by
    obtain ⟨p, n⟩ := i
    obtain rfl : j = (p + 1, n + 1) := hij.symm
    obtain rfl : k = (p, n + 1) := by
      rw [← hjk]; ext <;> simp
    exact ShortComplex.exact_mk_of_eq _ _ (F.couplef_self p n) (F.coupleα_self p (n + 1))
      ((F.ses_shortExact p).homology_exact₁ n (n + 1) rfl)

@[simp] lemma exactCouple_D (i : ℤ × ℤ) : F.exactCouple.D i = (F.piece i.1).homology i.2 := rfl
@[simp] lemma exactCouple_E (i : ℤ × ℤ) : F.exactCouple.E i = (F.gr i.1).homology i.2 := rfl

/-- The `E₁`-page differential `d₁ : Hⁿ(grᵖ K) ⟶ Hⁿ⁺¹(grᵖ⁺¹ K)` of the spectral sequence of a
filtered complex is the composite of the connecting homomorphism
`Hⁿ(grᵖ K) ⟶ Hⁿ⁺¹(Fᵖ⁺¹ K)` and of the projection `Hⁿ⁺¹(Fᵖ⁺¹ K) ⟶ Hⁿ⁺¹(grᵖ⁺¹ K)`.

(blueprint: `thm-sp-spectral-object-yields`) -/
lemma exactCouple_d (p n : ℤ) :
    F.exactCouple.d (p, n) (p + 1, n + 1) =
      (F.ses_shortExact p).δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap (cokernel.π _) (n + 1) := by
  rw [ExactCouple.d_eq _ (p, n) (p + 1, n + 1) _ rfl]
  exact congrArg₂ (· ≫ ·) (F.couplef_self p n) (F.coupleg_self (p + 1) (n + 1))

/-- The maps `Hⁿ(Fᵖ K) ⟶ Hⁿ(K)` induced by the inclusions of subcomplexes. -/
noncomputable def toHomology (p n : ℤ) : F.exactCouple.D (p, n) ⟶ K.homology n :=
  HomologicalComplex.homologyMap (F.F p).arrow n

lemma α_toHomology (p n : ℤ) :
    F.exactCouple.α (p + 1, n) (p, n) ≫ F.toHomology p n = F.toHomology (p + 1) n := by
  change F.coupleα _ _ ≫ _ = _
  rw [coupleα_self, toHomology, toHomology, ← HomologicalComplex.homologyMap_comp,
    Subobject.ofLE_arrow]

/-- The filtration `Fᵖ Hⁿ(K) = im (Hⁿ(Fᵖ K) ⟶ Hⁿ(K))` induced on the cohomology of a filtered
complex: the image filtration of the filtration of `K`.

(blueprint: `thm-sp-spectral-object-yields`, `def-sp-image-filtration`) -/
noncomputable def homologyFiltration (n : ℤ) : DecreasingFiltration (K.homology n) :=
  F.exactCouple.abutmentFiltration F.toHomology F.α_toHomology n

lemma isIso_homologyMap_of_isIso_f {L L' : CochainComplex C ℤ} (φ : L ⟶ L') (n : ℤ)
    (h₀ : IsIso (φ.f (n - 1))) (h₁ : IsIso (φ.f n)) (h₂ : IsIso (φ.f (n + 1))) :
    IsIso (HomologicalComplex.homologyMap φ n) := by
  have : IsIso (φ.f ((ComplexShape.up ℤ).prev n)) := by
    rwa [CochainComplex.prev]
  have : IsIso (φ.f ((ComplexShape.up ℤ).next n)) := by
    rwa [CochainComplex.next]
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
    (by change Epi (φ.f _); infer_instance)
    (by change IsIso (φ.f _); infer_instance) (by change Mono (φ.f _); infer_instance)

/-- **Convergence of the spectral sequence of a filtered complex.** If the filtration of `K` is
bounded in each degree (`Fᵖ Kⁿ = Kⁿ` for `p ≪ 0` and `Fᵖ Kⁿ = 0` for `p ≫ 0`), the spectral
sequence of the filtered complex converges to `H(K)` with the image filtration
`Fᵖ Hⁿ(K) = im (Hⁿ(Fᵖ K) ⟶ Hⁿ(K))`.

(blueprint: `thm-sp-spectral-object-yields`) -/
theorem convergesTo_exactCouple
    (hiso : ∀ n : ℤ, ∃ m : ℤ, ∀ p ≤ m, IsIso ((F.F p).arrow.f n))
    (hzero : ∀ n : ℤ, ∃ M : ℤ, ∀ p ≥ M, IsZero ((F.piece p).X n)) :
    F.exactCouple.ConvergesTo F.toHomology F.homologyFiltration := by
  refine F.exactCouple.convergesTo_abutmentFiltration F.toHomology F.α_toHomology ?_ ?_
  · intro n
    obtain ⟨m₀, h₀⟩ := hiso (n - 1)
    obtain ⟨m₁, h₁⟩ := hiso n
    obtain ⟨m₂, h₂⟩ := hiso (n + 1)
    exact ⟨min m₀ (min m₁ m₂), fun p hp ↦ isIso_homologyMap_of_isIso_f _ n
      (h₀ p (by omega)) (h₁ p (by omega)) (h₂ p (by omega))⟩
  · intro n
    obtain ⟨M, hM⟩ := hzero n
    refine ⟨M, fun p hp ↦ ?_⟩
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ (hM p hp)

end DecreasingFiltration

end CategoryTheory
