/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CurveProjection
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# Coherent cohomology of the projective line and of smooth projective curves

Let `k` be a field and `ℙ¹_k = ProjectiveLine (Spec k)`. This file records the cohomology of the
twisting sheaves `𝒪(d)` on `ℙ¹_k`, the vanishing of the cohomology of quasi-coherent sheaves on
`ℙ¹_k` in degrees `≥ 2`, the finiteness of the cohomology of coherent sheaves on `ℙ¹_k`, and the
finiteness of the cohomology of coherent sheaves on a smooth projective curve.

The twisting sheaves are `AlgebraicGeometry.ProjectiveSpace.twist`, which exist and are
invertible by `AlgebraicGeometry.ProjectiveSpace.isInvertible_twist`; that they are the twisted
structure sheaves of the standard cover, unique up to unique isomorphism, is
`AlgebraicGeometry.ProjectiveLine.nonempty_twistData` (blueprint
`theorem-riemann-roch-coherent-serre-duality`). The cohomology of the twists on `ℙ¹_k` is the case
`d = 1` of Serre's computation of the cohomology of `ℙᵈ_k`,
`lemma-coherent-base-change-invertible-sheaves--1`.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.nonempty_H_zero_twist_equiv_twistSectionPairs`: the global
  sections of `𝒪(d)` are the pairs `(p, q)` with `p(t) = tᵈ q(1/t)`.
- `AlgebraicGeometry.ProjectiveLine.nonempty_H_zero_twist_equiv`,
  `subsingleton_H_zero_twist_of_neg`, `subsingleton_H_one_twist`,
  `nonempty_H_one_twist_equiv_dual` and `nonempty_relativeDifferentials_iso_twist`: the
  cohomology of the twists, and `Ω¹_{ℙ¹/k} ≅ 𝒪(-2)`.
- `AlgebraicGeometry.ProjectiveLine.subsingleton_H_of_two_le`: `H^q(ℙ¹_k, ℱ) = 0` for `q ≥ 2`.
- `AlgebraicGeometry.ProjectiveLine.finiteDimensional_H`: `H⁰` and `H¹` of a coherent sheaf on
  `ℙ¹_k` are finite-dimensional.
- `AlgebraicGeometry.finiteDimensional_H_of_isCurve`: the cohomology of a coherent sheaf on a
  smooth projective curve over an algebraically closed field is finite-dimensional, and vanishes
  in degrees `≥ 2`.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial LaurentPolynomial

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveLine

variable (k : Type u) [Field k]

lemma natCard_ulift_fin_two : Nat.card (ULift.{u} (Fin 2)) = 1 + 1 := by
  simp

/-- The `k`-vector space of pairs `(p, q) ∈ k[t] × k[s]` with `p(t) = tᵈ q(1/t)` in
`k[t, t⁻¹]`: the global sections of the twisting sheaf `𝒪(d)` on `ℙ¹_k`, written through their
coefficients `p` on `U₀ = Spec k[t]` and `q` on `U₁ = Spec k[s]`, `s = 1/t`, with respect to the
generating sections `g₀`, `g₁` glued by `g₀ = t⁻ᵈ g₁`. -/
def twistSectionPairs (d : ℤ) : Submodule k (k[X] × k[X]) :=
  LinearMap.ker ((toLaurentAlg (R := k)).toLinearMap ∘ₗ LinearMap.fst k k[X] k[X] -
    LinearMap.mulLeft k (T d : k[T;T⁻¹]) ∘ₗ (invert (R := k)).toLinearMap ∘ₗ
      (toLaurentAlg (R := k)).toLinearMap ∘ₗ LinearMap.snd k k[X] k[X])

lemma mem_twistSectionPairs (d : ℤ) (pq : k[X] × k[X]) :
    pq ∈ twistSectionPairs k d ↔ toLaurent pq.1 = T d * invert (toLaurent pq.2) := by
  simp [twistSectionPairs, sub_eq_zero]

/-- A pair `(p, q)` lies in `twistSectionPairs k d` iff the coefficient of `tʲ` in `p` is that of
`s^{d - j}` in `q`, for every `j : ℤ`. -/
lemma mem_twistSectionPairs_iff_coeff (d : ℤ) (pq : k[X] × k[X]) :
    pq ∈ twistSectionPairs k d ↔
      ∀ j : ℤ, (toLaurent pq.1).coeff j = (toLaurent pq.2).coeff (d - j) := by
  rw [mem_twistSectionPairs]
  refine ⟨fun h j ↦ ?_, fun h ↦ LaurentPolynomial.ext fun j ↦ ?_⟩ <;>
  · rw [h, coeff_T_mul, invert_apply, neg_sub]

lemma twistSectionPairs_eq_bot {d : ℤ} (hd : d < 0) : twistSectionPairs k d = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun ⟨p, q⟩ h ↦ ?_
  rw [mem_twistSectionPairs_iff_coeff] at h
  refine Prod.ext (Polynomial.ext fun j ↦ ?_) (Polynomial.ext fun j ↦ ?_)
  · rw [← coeff_toLaurent_natCast, h, coeff_toLaurent_of_neg _ (by omega)]
    rfl
  · have := h (d - j)
    rw [sub_sub_cancel, coeff_toLaurent_of_neg _ (by omega)] at this
    rw [← coeff_toLaurent_natCast, ← this]
    rfl

/-- For `D ≥ 0`, the coefficients of `p` in degrees `≤ D` of a pair `(p, q)` in
`twistSectionPairs k D`; they determine the pair (`bijective_twistSectionPairsCoeff`). -/
def twistSectionPairsCoeff (D : ℕ) : twistSectionPairs k D →ₗ[k] (Fin (D + 1) → k) where
  toFun x j := x.1.1.coeff j
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

lemma bijective_twistSectionPairsCoeff (D : ℕ) :
    Function.Bijective (twistSectionPairsCoeff k D) := by
  refine ⟨fun ⟨⟨p, q⟩, h⟩ ⟨⟨p', q'⟩, h'⟩ hpq ↦ ?_, fun a ↦ ?_⟩
  · rw [mem_twistSectionPairs_iff_coeff] at h h'
    have hp : ∀ j : ℕ, p.coeff j = p'.coeff j := fun j ↦ by
      rcases le_or_gt j D with hj | hj
      · exact congrFun hpq ⟨j, by omega⟩
      · rw [← coeff_toLaurent_natCast, ← coeff_toLaurent_natCast, h, h',
          coeff_toLaurent_of_neg _ (by omega), coeff_toLaurent_of_neg _ (by omega)]
    have hq : ∀ j : ℕ, q.coeff j = q'.coeff j := fun j ↦ by
      have e := h (D - j)
      have e' := h' (D - j)
      rw [sub_sub_cancel] at e e'
      rw [← coeff_toLaurent_natCast, ← coeff_toLaurent_natCast, ← e, ← e']
      rcases le_or_gt j D with hj | hj
      · have : ((D : ℤ) - j) = ((D - j : ℕ) : ℤ) := by omega
        rw [this, coeff_toLaurent_natCast, coeff_toLaurent_natCast, hp]
      · rw [coeff_toLaurent_of_neg _ (by omega), coeff_toLaurent_of_neg _ (by omega)]
    exact Subtype.ext (Prod.ext (Polynomial.ext hp) (Polynomial.ext hq))
  · refine ⟨⟨⟨∑ j : Fin (D + 1), Polynomial.C (a j) * X ^ (j : ℕ),
      ∑ j : Fin (D + 1), Polynomial.C (a j) * X ^ (D - j : ℕ)⟩, ?_⟩, ?_⟩
    · rw [mem_twistSectionPairs]
      simp only [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have : ((D - j : ℕ) : ℤ) = D - j := by omega
      simp [this]
    · funext i
      change (∑ j : Fin (D + 1), Polynomial.C (a j) * X ^ (j : ℕ)).coeff i = a i
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i (fun j _ hj ↦ by
        rw [coeff_C_mul_X_pow, ite_eq_right (fun h ↦ hj (Fin.ext h.symm))]) (by simp)]
      simp

/-- The exponent vectors of the monomials of degree `D` in the two variables `x₀, x₁` are
determined by the exponent of `x₁`, which is at most `D`. -/
def degreeEqEquivFin (D : ℕ) :
    {s : ULift.{u} (Fin 2) →₀ ℕ | s.degree = D} ≃ Fin (D + 1) where
  toFun s := ⟨s.1 ⟨1⟩, by
    have h : s.1.degree = D := s.2
    rw [Finsupp.degree_eq_sum, ← Equiv.ulift.symm.sum_comp, Fin.sum_univ_two] at h
    change s.1 ⟨0⟩ + s.1 ⟨1⟩ = D at h
    omega⟩
  invFun j := ⟨Finsupp.single (ULift.up 0) (D - j) + Finsupp.single (ULift.up 1) (j : ℕ), by
    change Finsupp.degree _ = D
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega⟩
  left_inv s := by
    have h : s.1.degree = D := s.2
    rw [Finsupp.degree_eq_sum, ← Equiv.ulift.symm.sum_comp, Fin.sum_univ_two] at h
    change s.1 ⟨0⟩ + s.1 ⟨1⟩ = D at h
    refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
    obtain ⟨i⟩ := i
    fin_cases i <;> simp; omega
  right_inv j := by
    ext
    simp

/-- **Sections of the twists.** The global sections of `𝒪(d)` on `ℙ¹_k` are the pairs
`(p, q) ∈ k[t] × k[s]` with `p(t) = tᵈ q(1/t)` in `k[t, t⁻¹]`.

Only the existence of a `k`-linear isomorphism is asserted: the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist` is not constructed from the generating sections
`g₀, g₁` of the blueprint, so the isomorphism is not pinned down as "taking coefficients".

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem nonempty_H_zero_twist_equiv_twistSectionPairs (d : ℤ) :
    Nonempty ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 0 ≃ₗ[k]
      twistSectionPairs k d) := by
  rcases lt_or_ge d 0 with hd | hd
  · obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology (ULift.{u} (Fin 2)) k d 0
    have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_zero (ULift.{u} (Fin 2)) k hd
    have := e.toEquiv.subsingleton
    have : Subsingleton (twistSectionPairs k d) := by
      rw [twistSectionPairs_eq_bot k hd]
      infer_instance
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · lift d to ℕ using hd
    obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_zero_twist_equiv _ k 1 natCard_ulift_fin_two d
    exact ⟨e ≪≫ₗ ((ProjectiveSpace.homogeneousSubmoduleBasis _ k d).reindex
      (degreeEqEquivFin d)).equivFun ≪≫ₗ
        (LinearEquiv.ofBijective _ (bijective_twistSectionPairsCoeff k d)).symm⟩

/-- **Global sections of the twists on `ℙ¹_k`, `d ≥ 0`.** `H⁰(ℙ¹_k, 𝒪(d))` is the space of
homogeneous polynomials of degree `d` in `k[x₀, x₁]`, of dimension `d + 1`.

This is part (i) of the blueprint lemma, the case `ℙ¹` of
`AlgebraicGeometry.ProjectiveSpace.nonempty_H_zero_twist_equiv`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem nonempty_H_zero_twist_equiv (d : ℕ) :
    Nonempty ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 0 ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k d) :=
  ProjectiveSpace.nonempty_H_zero_twist_equiv _ k 1 (natCard_ulift_fin_two) d

/-- **Global sections of the twists on `ℙ¹_k`, `d < 0`.** `H⁰(ℙ¹_k, 𝒪(d)) = 0` for `d < 0`:
a pair `(p, q)` with `p(t) = tᵈ q(1/t)` has `p = q = 0`, since every exponent of `tᵈ q(1/t)` is
negative.

This is the second half of part (i) of the blueprint lemma.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem subsingleton_H_zero_twist_of_neg (d : ℤ) (hd : d < 0) :
    Subsingleton ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 0) := by
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology (ULift.{u} (Fin 2)) k d 0
  have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_zero (ULift.{u} (Fin 2)) k hd
  exact e.toEquiv.subsingleton

/-- **`H¹` of the twists on `ℙ¹_k`, `d ≥ -1`.** `H¹(ℙ¹_k, 𝒪(d)) = 0` for `d ≥ -1`.

This is the first half of part (ii) of the blueprint lemma, the case `ℙ¹` of
`AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_top`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem subsingleton_H_one_twist (d : ℤ) (hd : -1 ≤ d) :
    Subsingleton ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 1) :=
  ProjectiveSpace.subsingleton_H_twist_top _ k 1 one_ne_zero natCard_ulift_fin_two d
    (by simpa using hd)

/-- **`H¹` of the twists on `ℙ¹_k`, `d ≤ -2`.** `H¹(ℙ¹_k, 𝒪(d))` is dual to the space of
homogeneous polynomials of degree `-d-2` in `k[x₀, x₁]`; in particular it has dimension `-d-1`,
and `H¹(ℙ¹_k, 𝒪(-2)) ≅ k`.

This is the second half of part (ii) of the blueprint lemma, the case `ℙ¹` of
`AlgebraicGeometry.ProjectiveSpace.nonempty_H_twist_top_equiv_dual`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem nonempty_H_one_twist_equiv_dual (d : ℤ) (hd : d ≤ -2) :
    Nonempty ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 1 ≃ₗ[k]
      Module.Dual k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k (-d - 2).toNat)) :=
  have h : -d - ((1 : ℕ) : ℤ) - 1 = -d - 2 := by push_cast; ring
  h ▸ ProjectiveSpace.nonempty_H_twist_top_equiv_dual _ k 1 natCard_ulift_fin_two d
    (by simpa using hd)

/-- **The canonical sheaf of `ℙ¹_k`.** `Ω¹_{ℙ¹/k} ≅ 𝒪(-2)`: with the trivialisations `dt` on
`U₀` and `ds` on `U₁`, `s = 1/t`, one has `dt = -t² ds`, and the transition function `-t²`
differs from the transition function `t²` of `𝒪(-2)` by the unit `-1`.

This is part (iii) of the blueprint lemma.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem nonempty_relativeDifferentials_iso_twist :
    Nonempty ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)) :=
  ⟨relativeDifferentialsIsoTwist k⟩

/-- **Vanishing above the dimension on `ℙ¹_k`.** For every quasi-coherent `𝒪_{ℙ¹_k}`-module `ℱ`,
`H^q(ℙ¹_k, ℱ) = 0` for all `q ≥ 2`: the Čech complex of the standard cover by the two affine
opens `U₀`, `U₁` computes the cohomology of `ℱ`, and has length two.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem subsingleton_H_of_two_le (ℱ : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) ℱ]
    {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (ℱ.H q) :=
  ProjectiveSpace.subsingleton_H_of_lt _ k natCard_ulift_fin_two ℱ hq

/-- **Finite coherent cohomology on the projective line.** For every coherent
`𝒪_{ℙ¹_k}`-module `ℱ`, `H⁰(ℙ¹_k, ℱ)` and `H¹(ℙ¹_k, ℱ)` are finite-dimensional over `k`: they
are the kernel and the cokernel of the Čech differential
`Γ(U₀, ℱ) ⊕ Γ(U₁, ℱ) → Γ(U₀ ∩ U₁, ℱ)` of the standard cover.

As elsewhere, "coherent" is spelled as quasi-coherent and of finite presentation.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem finiteDimensional_H (ℱ : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) ℱ]
    {q : ℕ} (hq : q ≤ 1) : FiniteDimensional k (ℱ.H q) :=
  -- the bound `q ≤ 1` is not needed: `ℙ¹_k` is proper over `k`
  (fun _ ↦ Scheme.Modules.finiteDimensional_H_of_isProper ℱ q) hq

end ProjectiveLine

/-- **Coherent cohomology of a smooth projective curve over an algebraically closed field.** Let
`k` be algebraically closed, `X` a smooth projective curve over `k` (an integral scheme of
dimension one, smooth over `k`, with a closed immersion `i` into some `ℙⁿ_k` over `k`), and `ℱ`
a coherent `𝒪_X`-module. Then `H⁰(X, ℱ)` and `H¹(X, ℱ)` are finite-dimensional over `k`, and
`H^q(X, ℱ) = 0` for `q ≥ 2`.

The finiteness holds since `X` is proper over `k`
(`AlgebraicGeometry.Scheme.Modules.finiteDimensional_H_of_isProper`). For the vanishing, choose
a finite morphism `u : X ⟶ ℙ¹_k` (`AlgebraicGeometry.exists_isFinite_toProjectiveLine`). Since
`u` is affine, the preimages of the two standard affine opens `U₀`, `U₁` of `ℙ¹_k` are affine
opens covering `X`, and `X` is separated, so the quasi-coherent cohomology of `X` vanishes in
degrees `≥ 2` (`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_card_le`), as on `ℙ¹_k`
(`AlgebraicGeometry.ProjectiveLine.subsingleton_H_of_two_le`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem finiteDimensional_H_of_isCurve {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsIntegral X] [IsCurve (X ↘ Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] (hX : topologicalKrullDim X = 1) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i]
    (hi : i ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k) = X ↘ Spec (.of k)) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    FiniteDimensional k (ℱ.H 0) ∧ FiniteDimensional k (ℱ.H 1) ∧
      ∀ q, 2 ≤ q → Subsingleton (ℱ.H q) := by
  classical
  have : IsProper (X ↘ Spec (.of k)) := hi ▸ inferInstance
  have : i.IsOver (Spec (.of k)) := ⟨hi⟩
  refine ⟨Scheme.Modules.finiteDimensional_H_of_isProper ℱ 0,
    Scheme.Modules.finiteDimensional_H_of_isProper ℱ 1, fun q hq ↦ ?_⟩
  obtain ⟨π, hπ, -⟩ := exists_isFinite_toProjectiveLine X i hX
  have : IsSeparated (Limits.terminal.from X) := by
    rw [← Limits.terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  have hcard : (Finset.univ : Finset (ULift.{u} (Fin 2))).card = 2 := by simp
  exact Scheme.Modules.subsingleton_H_of_card_le Finset.univ Finset.univ_nonempty
    (fun j ↦ π ⁻¹ᵁ ProjectiveSpace.standardOpen _ (Spec (.of k)) j)
    (fun j _ ↦ (ProjectiveSpace.isAffineOpen_standardOpen _ _ j).preimage π)
    (by rw [Finset.sup_univ_eq_iSup, ← Scheme.Hom.preimage_iSup,
      ProjectiveSpace.iSup_standardOpen, Scheme.Hom.preimage_top])
    _ (Scheme.Modules.cechAcyclicOnAffines_of_isQuasicoherent ℱ) (hcard ▸ hq)

end AlgebraicGeometry
