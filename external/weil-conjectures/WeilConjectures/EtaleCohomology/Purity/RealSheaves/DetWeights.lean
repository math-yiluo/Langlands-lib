/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne
public import WeilConjectures.RepresentationTheory.CompositionFactors

/-!
# Determinant weights of lisse Weil sheaves

Let `W` be the Weil group of a smooth geometrically connected curve `C₀ / 𝔽_q`, `ℓ ≠ p`, and
`ι : ℚ̄_ℓ →+* ℂ`. The determinant line `det ρ = ⋀^{rank ρ} ρ` of a lisse Weil representation is
a rank-one lisse sheaf, hence punctually `ι`-pure of a unique weight `a` (rank-one purity,
`theorem-rank-one-sheaves-have-finite`), and the *determinant weight* of `ρ` is
`dw_ι(ρ) = a / rank ρ` (blueprint subsection `definition-determinant-weight--1`).

This file defines `dw_ι` (`AlgebraicGeometry.WeilGroup.detWeight`) as the weight read off from
the chosen Frobenius lift, `wt_{ι, q}(det ρ(γ)) / rank ρ`, and proves that it is the unique
`a / r` making `det ρ` pure of weight `a`. It then defines the multiset of determinant weights
of the composition factors of a finite-dimensional Weil representation, its rank-counted
version, and the numbers `N_γ` and `B_γ`, and proves that they do not depend on the
composition series (Jordan–Hölder).

## Main definitions

- `AlgebraicGeometry.WeilGroup.detWeight`: the determinant weight `dw_ι(ρ)`.
- `AlgebraicGeometry.WeilGroup.detWeightMultiset`: the determinantal-weight multiset.
- `AlgebraicGeometry.WeilGroup.rankDetWeightMultiset`: the rank-counted list.
- `AlgebraicGeometry.WeilGroup.rankAbove`, `AlgebraicGeometry.WeilGroup.weightSumAbove`:
  `N_γ` and `B_γ`.
- `AlgebraicGeometry.WeilGroup.weightBlock`: the weight block `𝒮(γ)`.

## Main statements

- `AlgebraicGeometry.WeilGroup.existsUnique_isPunctuallyPure_detLine`: the determinant line of
  a lisse Weil sheaf is pure of exactly one weight.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_detLine_iff_eq_mul_detWeight`: that weight is
  `rank ρ * dw_ι(ρ)`.
- `AlgebraicGeometry.WeilGroup.hasFiniteGeometricDet_and_detWeight_eq`: `dw_ι` agrees with the
  determinant weight `dw_{λ_ι}` of `definition-determinant-weight--1` for the real weight character
  `λ_ι`.
- `AlgebraicGeometry.WeilGroup.detWeightMultiset_eq`,
  `AlgebraicGeometry.WeilGroup.rankDetWeightMultiset_eq`: independence of the composition series.
- `AlgebraicGeometry.WeilGroup.rankAbove_eq_sum`,
  `AlgebraicGeometry.WeilGroup.weightSumAbove_eq_sum`,
  `AlgebraicGeometry.WeilGroup.weightBlock_eq_iSup`: the description for a semisimple sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
  (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `definition-determinant-weight--1`: Determinantal weight.

The determinant weight `dw_ι(ρ) = a / r` of a Weil representation `ρ` of rank `r`, where
`a = wt_{ι, q}(det ρ(γ)) = 2 log |ι det ρ(γ)| / log q` for the chosen Frobenius lift `γ` of
degree one. For a lisse `ρ`, `a` is the unique weight of which the determinant line `det ρ` is
punctually `ι`-pure (`AlgebraicGeometry.WeilGroup.existsUnique_isPunctuallyPure_detLine` and
`AlgebraicGeometry.WeilGroup.isPunctuallyPure_detLine_iff_eq_mul_detWeight`), which is the
definition of the blueprint; it involves no choice of a coefficient field, the coefficients
being `ℚ̄_ℓ` throughout (compare `corollary-determinant-weights--2`). For `V = 0`
it is the junk value `0`. -/
noncomputable def detWeight : ℝ :=
  frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift)) /
    Module.finrank (PadicAlgCl l) V

variable {W l ρ}

/-- Equivalent representations have the same determinant weight. -/
theorem detWeight_of_equiv {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
    {σ : Representation (PadicAlgCl l) W.carrier V'} (e : ρ.Equiv σ) :
    W.detWeight l σ ι = W.detWeight l ρ ι := by
  rw [detWeight, detWeight, e.det_apply, e.finrank_eq]

/-- The determinant weight `dw_ι` is the determinant weight of `definition-determinant-weight--1`
for the real weight character `λ_ι = wt_{ι, q}` and the chosen Frobenius lift. -/
theorem detWeight_eq_detWeight_weightCharacter (σ : Representation (PadicAlgCl l) W.carrier V) :
    W.detWeight l σ ι = σ.detWeight (weightCharacter ι (Nat.card K)) W.frobeniusLift :=
  (detWeight_weightCharacter ι σ _ _).symm

section DetLine

variable [FiniteDimensional (PadicAlgCl l) V]

/-- The determinant line has the single local eigenvalue `det ρ(F_x)` at a closed point `x`. -/
theorem localEigenvalues_detLine (x : C.finitePoints) :
    W.localEigenvalues l (W.detLine l ρ) x = {LinearMap.det (ρ (W.frobenius x))} := by
  have hcard : Multiset.card (ρ (W.frobenius x)).charpoly.roots =
      Module.finrank (PadicAlgCl l) V := by
    rw [← LinearMap.charpoly_natDegree (ρ (W.frobenius x))]
    exact (Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits (ρ (W.frobenius x)).charpoly))
  change (_root_.exteriorPower.map (Module.finrank (PadicAlgCl l) V)
    (ρ (W.frobenius x))).charpoly.roots = _
  rw [LinearMap.charpoly_roots_exteriorPower, ← hcard, Multiset.powersetCard_self,
    Multiset.map_singleton, ← Module.End.det_eq_prod_roots_charpoly_of_splits
      (IsAlgClosed.splits _)]

/-- The determinant line is punctually `ι`-pure of weight `a` exactly when
`wt_{ι, q_x}(det ρ(F_x)) = a` at every closed point `x`. -/
theorem isPunctuallyPure_detLine_iff {a : ℝ} :
    W.IsPunctuallyPure l (W.detLine l ρ) ι a ↔
      ∀ x : C.finitePoints,
        frobeniusWeight ι (C.pointNorm x.1) (LinearMap.det (ρ (W.frobenius x))) = a := by
  simp only [IsPunctuallyPure, localEigenvalues_detLine, Multiset.mem_singleton, forall_eq]

/-- `ρ` has determinant weight `γ` in the sense of `AlgebraicGeometry.WeilGroup.HasDetWeight`
exactly when its determinant line is punctually `ι`-pure of weight `rank ρ * γ`. -/
theorem hasDetWeight_iff_isPunctuallyPure_detLine {γ : ℝ} :
    W.HasDetWeight l ρ ι γ ↔
      W.IsPunctuallyPure l (W.detLine l ρ) ι (Module.finrank (PadicAlgCl l) V * γ) := by
  rw [isPunctuallyPure_detLine_iff]
  rfl

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- A Weil group of a curve has a closed point to evaluate local Frobenius elements at. -/
theorem nonempty_finitePoints (W : WeilGroup p) : Nonempty C.finitePoints := by
  have := W.connectedSpace
  obtain ⟨x, hx⟩ := p.exists_mem_finitePoints
  exact ⟨⟨x, hx⟩⟩

/-- Blueprint `corollary-determinant-weights--2`: The determinant weight does not
depend on the coefficient field.

Let `ρ` be a representation of the Weil group defined over a field `E`, and `E'` an extension
of `E` with an embedding `ι : E' →+* ℂ`. The local eigenvalue of the determinant line of `ρ`
at `x` is `det ρ(F_x)`; read with coefficients in `E'`, it is the determinant of the base
change of `ρ(F_x)` to `E'`, which is the image of `det ρ(F_x)`. Hence `det ρ` is punctually
`ι`-pure of weight `a` with coefficients in `E` if and only if it is with coefficients in
`E'`. -/
theorem isPunctuallyPure_det_baseChange_iff {E E' : Type*} [Field E] [Field E'] [Algebra E E']
    (ι' : E' →+* ℂ) {U : Type*} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (σ : Representation E W.carrier U) (a : ℝ) :
    (∀ x : C.finitePoints, frobeniusWeight (ι'.comp (algebraMap E E')) (C.pointNorm x.1)
        (LinearMap.det (σ (W.frobenius x))) = a) ↔
      ∀ x : C.finitePoints, frobeniusWeight ι' (C.pointNorm x.1)
        (LinearMap.det ((σ (W.frobenius x)).baseChange E')) = a := by
  simp only [LinearMap.det_baseChange, frobeniusWeight, RingHom.comp_apply]

end DetLine

section RankOne

variable [FiniteDimensional (PadicAlgCl l) V] [SmoothOfRelativeDimension 1 p]
  [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient]

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient] in
/-- The determinant of a lisse Weil representation is continuous on the geometric part: in a
basis it is a polynomial in the matrix coefficients. -/
theorem IsLisse.continuous_det_apply (hρ : W.IsLisse l ρ) :
    Continuous fun g : W.geometric ↦ (ρ.detCharacter g : PadicAlgCl l) := by
  let b := Module.finBasis (PadicAlgCl l) V
  have h : Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ hρ.continuous_toMatrix b i j
  simpa only [Representation.coe_detCharacter_apply, LinearMap.det_toMatrix] using h.matrix_det

/-- The determinant line of a lisse Weil representation is punctually `ι`-pure of weight
`wt_{ι, q}(det ρ(γ))`, by rank-one purity (`corollary-rank-one-weights--1`). -/
theorem IsLisse.isPunctuallyPure_detLine (hρ : W.IsLisse l ρ) :
    W.IsPunctuallyPure l (W.detLine l ρ) ι
      (frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift))) := by
  rw [isPunctuallyPure_detLine_iff]
  intro x
  rw [← Representation.coe_detCharacter_apply, ← Representation.coe_detCharacter_apply]
  exact W.frobeniusWeight_eq_of_continuous ρ.detCharacter hρ.continuous_det_apply ι x

/-- Blueprint `corollary-determinant-weights--1`: Purity of the determinant line.

The determinant line `det ρ` of a lisse Weil sheaf `ρ` on the curve is punctually `ι`-pure of
exactly one real weight `a`: it is a rank-one lisse sheaf, with finite geometric image, hence
pure by rank-one purity; and `a` is unique because the curve has a closed point `y`, at which
`q_y ^ (a / 2) = |ι det ρ(F_y)|` determines `a`. -/
theorem existsUnique_isPunctuallyPure_detLine (hρ : W.IsLisse l ρ) :
    ∃! a : ℝ, W.IsPunctuallyPure l (W.detLine l ρ) ι a := by
  obtain ⟨x₀⟩ := W.nonempty_finitePoints
  refine ⟨_, hρ.isPunctuallyPure_detLine ι, fun a ha ↦ ?_⟩
  have ha' := (isPunctuallyPure_detLine_iff ι).1 ha
  have h := (isPunctuallyPure_detLine_iff ι).1 (hρ.isPunctuallyPure_detLine ι)
  exact (ha' x₀).symm.trans (h x₀)

/-- A lisse Weil representation has determinant weight `dw_ι(ρ)` in the sense of
`AlgebraicGeometry.WeilGroup.HasDetWeight`. -/
theorem IsLisse.hasDetWeight_detWeight (hρ : W.IsLisse l ρ) :
    W.HasDetWeight l ρ ι (W.detWeight l ρ ι) := by
  rw [hasDetWeight_iff_isPunctuallyPure_detLine, detWeight]
  rcases eq_or_ne (Module.finrank (PadicAlgCl l) V) 0 with h0 | h0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    rw [isPunctuallyPure_detLine_iff]
    intro x
    rw [LinearMap.det_eq_one_of_subsingleton, h0]
    simp [frobeniusWeight]
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 h0)]
    exact hρ.isPunctuallyPure_detLine ι

/-- For a nonzero lisse Weil representation of rank `r`, the determinant line is punctually
`ι`-pure of weight `a` exactly when `a = r * dw_ι(ρ)`; that is, `dw_ι(ρ) = a / r` for the
unique weight `a` of `corollary-determinant-weights--1`, which is the definition
`definition-determinant-weight--1` of the blueprint. -/
theorem isPunctuallyPure_detLine_iff_eq_mul_detWeight (hρ : W.IsLisse l ρ) {a : ℝ} :
    W.IsPunctuallyPure l (W.detLine l ρ) ι a ↔
      a = Module.finrank (PadicAlgCl l) V * W.detWeight l ρ ι := by
  have h := (hasDetWeight_iff_isPunctuallyPure_detLine ι).1 (hρ.hasDetWeight_detWeight ι)
  refine ⟨fun ha ↦ (existsUnique_isPunctuallyPure_detLine ι hρ).unique ha h, ?_⟩
  rintro rfl
  exact h

/-- The determinant weight is the only determinant weight of a nonzero lisse Weil
representation. -/
theorem HasDetWeight.detWeight_eq [Nontrivial V] (hρ : W.IsLisse l ρ) {γ : ℝ}
    (h : W.HasDetWeight l ρ ι γ) : W.detWeight l ρ ι = γ := by
  obtain ⟨x₀⟩ := W.nonempty_finitePoints
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (((hρ.hasDetWeight_detWeight ι) x₀).symm.trans (h x₀))

/-- Blueprint `corollary-determinant-weights--1`: Rank-one purity discharges the
finite-determinant hypotheses.

A lisse Weil sheaf `ρ` has finite geometric determinant in the sense of
`definition-determinant-weight--1` (the determinant character takes finitely many values on `π₁(C)`,
by the finite geometric image result applied to its determinant line), and its determinant weight
`dw_ι(ρ)` is the determinant weight `dw_{λ_ι}(ρ)` of `definition-determinant-weight--1` for the real
weight character `λ_ι(a) = 2 log |ι a| / log q` (`AlgebraicGeometry.WeilGroup.weightCharacter`) and
the degree one element `γ`. -/
theorem hasFiniteGeometricDet_and_detWeight_eq (hρ : W.IsLisse l ρ) :
    ρ.HasFiniteGeometricDet W.deg ∧
      W.detWeight l ρ ι = ρ.detWeight (weightCharacter ι (Nat.card K)) W.frobeniusLift :=
  ⟨W.finite_range_of_continuous ρ.detCharacter hρ.continuous_det_apply,
    (detWeight_weightCharacter ι ρ _ _).symm⟩

end RankOne

section Multiset

variable [FiniteDimensional (PadicAlgCl l) V]

variable (W l ρ) in
/-- Blueprint `definition-determinant-weight--2`: Determinantal-weight multiset.

The multiset of the determinant weights `dw_ι(S)` of the composition factors `S` of a
finite-dimensional Weil representation `ρ`, with one entry for every factor. These factors are
the simple summands of the semisimplification `ρ^{ss}`, counted with multiplicity; the multiset is
computed from a chosen composition series, and it does not depend on that choice
(`AlgebraicGeometry.WeilGroup.detWeightMultiset_eq`). These are the *constituent determinant
weights* of item 1 of `theorem-purity-real-sheaves-curves`. -/
noncomputable def detWeightMultiset : Multiset ℝ :=
  Subrepresentation.factorMultiset ρ fun N M ↦ W.detWeight l (M.subquotient N) ι

/-- The determinantal-weight multiset can be computed from any composition series
`0 = F 0 ⋖ ⋯ ⋖ F n = ρ` (Jordan–Hölder). -/
theorem detWeightMultiset_eq {n : ℕ} {F : ℕ → Subrepresentation ρ} (hF0 : F 0 = ⊥)
    (hFn : F n = ⊤) (hF : ∀ i < n, F i ⋖ F (i + 1)) :
    W.detWeightMultiset l ρ ι = (Finset.univ : Finset (Fin n)).val.map
      fun i : Fin n ↦ W.detWeight l ((F ((i : ℕ) + 1)).subquotient (F i)) ι :=
  Subrepresentation.factorMultiset_eq _ (fun _ _ _ _ ⟨e⟩ ↦ (detWeight_of_equiv ι e).symm) hF0
    hFn hF

/-- The entries of the determinantal-weight multiset are exactly the determinant weights of the
irreducible subquotients of `ρ` (Jordan–Hölder). -/
theorem mem_detWeightMultiset_iff {a : ℝ} :
    a ∈ W.detWeightMultiset l ρ ι ↔ ∃ U S : Subrepresentation ρ,
      (S.subquotient U).IsIrreducible ∧ W.detWeight l (S.subquotient U) ι = a := by
  obtain ⟨F, hF0, hFn, hF⟩ := ρ.exists_compositionSeries.some.exists_chain
  rw [detWeightMultiset_eq ι hF0 hFn hF, Multiset.mem_map]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨F i, F (i + 1),
      (Subrepresentation.isIrreducible_subquotient_iff (hF i i.2).le).2 (hF i i.2), rfl⟩
  · rintro ⟨U, S, hirr, rfl⟩
    obtain ⟨i, ⟨e⟩⟩ :=
      Subrepresentation.exists_equiv_of_isIrreducible_subquotient hF0 hFn hF hirr
    exact ⟨i, Finset.mem_univ_val i, detWeight_of_equiv ι e⟩

variable (W l ρ) in
/-- Blueprint `theorem-purity-real-sheaves-curves`: Rank-counted determinant weights and weight
blocks.

The *rank-counted list* of determinant weights of `ρ` (item 2): the multiset in which the
determinant weight `dw_ι(S)` of every composition factor `S` of `ρ` is repeated `rank S` times.
It does not depend on the composition series
(`AlgebraicGeometry.WeilGroup.rankDetWeightMultiset_eq`) and has `rank ρ` entries
(`AlgebraicGeometry.WeilGroup.card_rankDetWeightMultiset`). -/
noncomputable def rankDetWeightMultiset : Multiset ℝ :=
  (Subrepresentation.factorMultiset ρ fun N M ↦ Multiset.replicate
    (Module.finrank (PadicAlgCl l) (M.toSubmodule ⧸ N.toSubmodule.comap M.toSubmodule.subtype))
    (W.detWeight l (M.subquotient N) ι)).join

/-- The rank-counted list of determinant weights can be computed from any composition series
`0 = F 0 ⋖ ⋯ ⋖ F n = ρ` (Jordan–Hölder). -/
theorem rankDetWeightMultiset_eq {n : ℕ} {F : ℕ → Subrepresentation ρ} (hF0 : F 0 = ⊥)
    (hFn : F n = ⊤) (hF : ∀ i < n, F i ⋖ F (i + 1)) :
    W.rankDetWeightMultiset l ρ ι = ∑ i : Fin n, Multiset.replicate
      (Module.finrank (PadicAlgCl l) ((F ((i : ℕ) + 1)).toSubmodule ⧸
        (F i).toSubmodule.comap (F ((i : ℕ) + 1)).toSubmodule.subtype))
      (W.detWeight l ((F ((i : ℕ) + 1)).subquotient (F i)) ι) := by
  rw [rankDetWeightMultiset, Subrepresentation.factorMultiset_eq _
    (fun _ _ _ _ ⟨e⟩ ↦ by rw [e.finrank_eq, detWeight_of_equiv ι e]) hF0 hFn hF,
    Multiset.join]
  rfl

/-- The rank-counted list of determinant weights has `rank ρ` entries. -/
theorem card_rankDetWeightMultiset :
    Multiset.card (W.rankDetWeightMultiset l ρ ι) = Module.finrank (PadicAlgCl l) V := by
  obtain ⟨F, hF0, hFn, hF⟩ := ρ.exists_compositionSeries.some.exists_chain
  rw [rankDetWeightMultiset_eq ι hF0 hFn hF, Multiset.card_sum]
  simp only [Multiset.card_replicate]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ Module.finrank (PadicAlgCl l)
      ((F (i + 1)).toSubmodule ⧸ (F i).toSubmodule.comap (F (i + 1)).toSubmodule.subtype)),
    Subrepresentation.sum_finrank_subquotient hF0 fun i hi ↦ (hF i hi).le, hFn,
    Subrepresentation.toSubmodule_top, finrank_top]

/-- The rank-counted list of determinant weights is additive in extensions: for a
subrepresentation `A`, it is the sum of those of `A` and of the quotient `ρ / A`, as a composition
series of `ρ` is obtained by concatenating composition series of `A` and of `ρ / A`. -/
theorem rankDetWeightMultiset_eq_add (A : Subrepresentation ρ) :
    W.rankDetWeightMultiset l ρ ι =
      W.rankDetWeightMultiset l A.toRepresentation ι + W.rankDetWeightMultiset l A.quotient ι := by
  obtain ⟨F₁, h₁0, h₁m, h₁⟩ := A.toRepresentation.exists_compositionSeries.some.exists_chain
  obtain ⟨F₂, h₂0, h₂n, h₂⟩ := A.quotient.exists_compositionSeries.some.exists_chain
  obtain ⟨F, hF0, hFn, hF, he₁, he₂⟩ :=
    Subrepresentation.exists_compositionSeries_append A h₁0 h₁m h₁ h₂0 h₂n h₂
  rw [rankDetWeightMultiset_eq ι hF0 hFn hF, rankDetWeightMultiset_eq ι h₁0 h₁m h₁,
    rankDetWeightMultiset_eq ι h₂0 h₂n h₂, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    obtain ⟨e⟩ := he₁ i i.2
    rw [Fin.val_castAdd, e.symm.finrank_eq, detWeight_of_equiv ι e.symm]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    obtain ⟨e⟩ := he₂ i i.2
    rw [Fin.val_natAdd, e.symm.finrank_eq, detWeight_of_equiv ι e.symm]

variable (W l ρ) in
/-- Blueprint `theorem-purity-real-sheaves-curves`: Rank-counted determinant weights and weight
blocks.

The rank `N_γ` above the weight `γ` (item 3): the number of entries `> γ` of the rank-counted
list of determinant weights. For a semisimple `ρ = ⨁ V_a` it is `∑_{dw_ι(V_a) > γ} rank V_a`
(`AlgebraicGeometry.WeilGroup.rankAbove_eq_sum`). -/
noncomputable def rankAbove (γ : ℝ) : ℕ :=
  Multiset.card ((W.rankDetWeightMultiset l ρ ι).filter (γ < ·))

variable (W l ρ) in
/-- Blueprint `theorem-purity-real-sheaves-curves`: Rank-counted determinant weights and weight
blocks.

The weight sum `B_γ` above the weight `γ` (item 3): the sum of the entries `> γ` of the
rank-counted list of determinant weights. For a semisimple `ρ = ⨁ V_a` it is
`∑_{dw_ι(V_a) > γ} rank V_a · dw_ι(V_a)` (`AlgebraicGeometry.WeilGroup.weightSumAbove_eq_sum`). -/
noncomputable def weightSumAbove (γ : ℝ) : ℝ :=
  ((W.rankDetWeightMultiset l ρ ι).filter (γ < ·)).sum

variable (W l ρ) in
/-- Blueprint `theorem-purity-real-sheaves-curves`: Rank-counted determinant weights and weight
blocks.

The *weight block* `ρ(γ)` of weight `γ` (item 3): the sum of all irreducible subrepresentations
of determinant weight `γ`. For a semisimple `ρ = ⨁ V_a` with `V_a` irreducible it is
`⨁_{dw_ι(V_a) = γ} V_a` (`AlgebraicGeometry.WeilGroup.weightBlock_eq_iSup`); defining it
intrinsically shows that it does not depend on the decomposition. -/
noncomputable def weightBlock (γ : ℝ) : Subrepresentation ρ :=
  ⨆ (S : Subrepresentation ρ) (_ : S.toRepresentation.IsIrreducible ∧
    W.detWeight l S.toRepresentation ι = γ), S

section Decomposition

variable {I : Type*} [Fintype I] [DecidableEq I] {Vs : I → Subrepresentation ρ}
  (hint : DirectSum.IsInternal fun a ↦ (Vs a).toSubmodule)
  (hVs : ∀ a, (Vs a).toRepresentation.IsIrreducible)
include hint hVs

/-- For a semisimple `ρ = ⨁ V_a` with `V_a` irreducible, the rank-counted list of determinant
weights repeats `dw_ι(V_a)` exactly `rank V_a` times: the partial sums `V_1 ⊕ ⋯ ⊕ V_b` form a
composition series. -/
theorem rankDetWeightMultiset_eq_sum :
    W.rankDetWeightMultiset l ρ ι = ∑ a, Multiset.replicate
      (Module.finrank (PadicAlgCl l) (Vs a).toSubmodule)
        (W.detWeight l (Vs a).toRepresentation ι) := by
  let e := Fintype.equivFin I
  have hind : iSupIndep (Vs ∘ e.symm) := by
    rw [← Subrepresentation.iSupIndep_toSubmodule_iff]
    exact (hint.submodule_iSupIndep).comp e.symm.injective
  have htop : ⨆ i, (Vs ∘ e.symm) i = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_iSup, Subrepresentation.toSubmodule_top,
      ← hint.submodule_iSup_eq_top]
    exact e.symm.iSup_comp (g := fun a ↦ (Vs a).toSubmodule)
  obtain ⟨F, hF0, hFn, hF, hequiv⟩ :=
    Subrepresentation.exists_compositionSeries_of_iSupIndep hind htop fun i ↦ hVs _
  rw [rankDetWeightMultiset_eq ι hF0 hFn hF, ← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  obtain ⟨f⟩ := hequiv i
  rw [← f.finrank_eq, ← detWeight_of_equiv ι f]
  rfl

/-- For a semisimple `ρ = ⨁ V_a` with `V_a` irreducible, the entries of the rank-counted list
satisfying a predicate `P` are the `dw_ι(V_a)` with `P (dw_ι(V_a))`, each repeated `rank V_a`
times. -/
theorem filter_rankDetWeightMultiset_eq_sum (P : ℝ → Prop) [DecidablePred P] :
    (W.rankDetWeightMultiset l ρ ι).filter P =
      ∑ a ∈ Finset.univ.filter (fun a ↦ P (W.detWeight l (Vs a).toRepresentation ι)),
        Multiset.replicate (Module.finrank (PadicAlgCl l) (Vs a).toSubmodule)
          (W.detWeight l (Vs a).toRepresentation ι) := by
  rw [rankDetWeightMultiset_eq_sum ι hint hVs, Finset.sum_filter]
  generalize (Finset.univ : Finset I) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.filter_add, ih]
    congr 1
    split_ifs with h
    · exact Multiset.filter_eq_self.2 fun x hx ↦ (Multiset.eq_of_mem_replicate hx) ▸ h
    · exact Multiset.filter_eq_nil.2 fun x hx ↦ (Multiset.eq_of_mem_replicate hx) ▸ h

/-- For a semisimple `ρ = ⨁ V_a` with `V_a` irreducible, `N_γ = ∑_{dw_ι(V_a) > γ} rank V_a`. -/
theorem rankAbove_eq_sum (γ : ℝ) :
    W.rankAbove l ρ ι γ =
      ∑ a ∈ Finset.univ.filter (fun a ↦ γ < W.detWeight l (Vs a).toRepresentation ι),
        Module.finrank (PadicAlgCl l) (Vs a).toSubmodule := by
  rw [rankAbove, filter_rankDetWeightMultiset_eq_sum ι hint hVs, Multiset.card_sum]
  simp only [Multiset.card_replicate]

/-- For a semisimple `ρ = ⨁ V_a` with `V_a` irreducible,
`B_γ = ∑_{dw_ι(V_a) > γ} rank V_a · dw_ι(V_a)`. -/
theorem weightSumAbove_eq_sum (γ : ℝ) :
    W.weightSumAbove l ρ ι γ =
      ∑ a ∈ Finset.univ.filter (fun a ↦ γ < W.detWeight l (Vs a).toRepresentation ι),
        Module.finrank (PadicAlgCl l) (Vs a).toSubmodule *
          W.detWeight l (Vs a).toRepresentation ι := by
  rw [weightSumAbove, filter_rankDetWeightMultiset_eq_sum ι hint hVs,
    ← Multiset.coe_sumAddMonoidHom, map_sum]
  simp only [Multiset.coe_sumAddMonoidHom, Multiset.sum_replicate, nsmul_eq_mul]

end Decomposition

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- For a semisimple `ρ = ⨁ V_a` with `V_a` irreducible, the weight block of weight `γ` is
`⨁_{dw_ι(V_a) = γ} V_a`: an irreducible subrepresentation `S` lies in the sum of the `V_a`
equivalent to it (Schur's lemma), all of which have determinant weight `dw_ι(S)`. -/
theorem weightBlock_eq_iSup {I : Type*} [Finite I] [DecidableEq I]
    {Vs : I → Subrepresentation ρ}
    (hint : DirectSum.IsInternal fun a ↦ (Vs a).toSubmodule)
    (hVs : ∀ a, (Vs a).toRepresentation.IsIrreducible) (γ : ℝ) :
    W.weightBlock l ρ ι γ = ⨆ (a) (_ : W.detWeight l (Vs a).toRepresentation ι = γ), Vs a := by
  refine le_antisymm (iSup₂_le fun S ⟨hS, hγ⟩ ↦ ?_) (iSup₂_le fun a ha ↦ ?_)
  · refine (Subrepresentation.le_iSup_of_isInternal hint hVs hS).trans
      (iSup₂_le fun a ⟨f⟩ ↦ ?_)
    exact le_iSup₂ (f := fun a (_ : W.detWeight l (Vs a).toRepresentation ι = γ) ↦ Vs a) a
      ((detWeight_of_equiv ι f).trans hγ)
  · exact le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : S.toRepresentation.IsIrreducible ∧
      W.detWeight l S.toRepresentation ι = γ) ↦ S) (Vs a) ⟨hVs a, ha⟩

end Multiset

end WeilGroup

end AlgebraicGeometry
