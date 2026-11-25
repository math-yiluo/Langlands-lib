/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.ZetaFunction.HasseWeil

/-!
# The `lean-eval` challenge `weil_conjectures`

The repository `leanprover/lean-eval` contains the problem `weil_conjectures` (submitted by
Junyan Xu), a statement of the Weil conjectures in terms of point counts and multisets of
Frobenius eigenvalues. This file states it verbatim
(`LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures`) and derives it from the main
theorem `AlgebraicGeometry.Scheme.weil_conjectures` of this repository.

The bridge consists of the following steps.

* A smooth geometrically irreducible morphism is geometrically integral, since smooth morphisms
  are geometrically reduced.
* The multiset `Aᵢ` is the multiset of inverse roots of the polynomial `Pᵢ` of the main
  theorem (and `0` for `i > 2 d`). The functional equation and the Riemann hypothesis of the
  main theorem are stated for the roots `z = α⁻¹`; they translate into the statements on the
  inverse roots. Invariance under automorphisms of `ℂ` and integrality follow from
  `Pᵢ ∈ ℤ[t]` and `Pᵢ(0) = 1`.
* The point counts are the alternating sums of power sums of inverse roots
  (`AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum_roots`), and the set of `E`-points of `X`
  only depends on `E` up to `F`-isomorphism, so only on `[E : F]`.

## Main statements

- `AlgebraicGeometry.GeometricallyIntegral.of_smooth_of_geometricallyIrreducible`
- `AlgebraicGeometry.IsWeilFactorization.inverseRoots_spec`: the properties of the multisets
  of inverse roots.
- `AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum_inverseRoots`: `N n = ∑ (-1) ^ i ∑ αⁿ`.
- `LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures`: the `lean-eval` statement.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial

noncomputable section

namespace AlgebraicGeometry

/-- A smooth geometrically irreducible morphism is geometrically integral: smooth morphisms
are geometrically reduced. -/
lemma GeometricallyIntegral.of_smooth_of_geometricallyIrreducible {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] [GeometricallyIrreducible f] : GeometricallyIntegral f :=
  .of_geometricallyReduced_of_geometricallyIrreducible f

/-- The multiset of inverse roots `α = z⁻¹` in `ℂ` of the polynomial `Pᵢ`, for `i ≤ 2 d`,
and `0` for `i > 2 d`. -/
def weilInverseRoots {d : ℕ} (P : Fin (2 * d + 1) → ℤ[X]) (i : ℕ) : Multiset ℂ :=
  if h : i < 2 * d + 1 then ((P ⟨i, h⟩).map (Int.castRingHom ℂ)).roots.map (·⁻¹) else 0

lemma weilInverseRoots_of_lt {d : ℕ} (P : Fin (2 * d + 1) → ℤ[X]) {i : ℕ}
    (h : i < 2 * d + 1) :
    weilInverseRoots P i = ((P ⟨i, h⟩).map (Int.castRingHom ℂ)).roots.map (·⁻¹) :=
  dite_eq_left h

/-- The complex roots of an integer polynomial are permuted by every automorphism of `ℂ`. -/
lemma map_roots_map_intCast_ringEquiv (p : ℤ[X]) (φ : ℂ ≃+* ℂ) :
    ((p.map (Int.castRingHom ℂ)).roots).map φ = (p.map (Int.castRingHom ℂ)).roots := by
  have h := roots_map_of_injective_of_card_eq_natDegree (f := (φ : ℂ →+* ℂ)) φ.injective
    (p := p.map (Int.castRingHom ℂ)) IsAlgClosed.card_roots_eq_natDegree
  rw [Polynomial.map_map, RingHom.ext_int ((φ : ℂ →+* ℂ).comp (Int.castRingHom ℂ))
    (Int.castRingHom ℂ)] at h
  exact h

lemma ne_zero_of_mem_roots_map_intCast {p : ℤ[X]} (h0 : p.coeff 0 = 1) {z : ℂ}
    (hz : z ∈ (p.map (Int.castRingHom ℂ)).roots) : z ≠ 0 := by
  rintro rfl
  have h := (mem_roots'.1 hz).2
  rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, h0] at h
  simp at h

/-- The inverse of a complex root of an integer polynomial with constant coefficient `1` is
an algebraic integer: it is a root of the reversed polynomial, which is monic. -/
lemma isIntegral_inv_of_mem_roots_map_intCast {p : ℤ[X]} (h0 : p.coeff 0 = 1) {z : ℂ}
    (hz : z ∈ (p.map (Int.castRingHom ℂ)).roots) : _root_.IsIntegral ℤ z⁻¹ := by
  let : Invertible z := invertibleOfNonzero (ne_zero_of_mem_roots_map_intCast h0 hz)
  refine ⟨p.reverse, ?_, ?_⟩
  · rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by rw [h0]; exact one_ne_zero),
      h0]
  · rw [← invOf_eq_inv, algebraMap_int_eq, eval₂_reverse_eq_zero_iff, ← Polynomial.eval_map]
    exact (mem_roots'.1 hz).2

lemma norm_inv_eq_sqrt {q : ℕ} (hq : 0 < q) (i : ℕ) {z : ℂ}
    (hz : ‖z‖ = (q : ℝ) ^ (-(i : ℝ) / 2)) : ‖z⁻¹‖ = √((q : ℝ) ^ i) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [norm_inv, hz, ← Real.rpow_neg hq'.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hq'.le]
  congr 1
  ring

/-- The multisets of inverse roots of polynomials `Pᵢ` satisfying the conclusions of the Weil
conjectures: `A₀ = {1}`, the functional equation `A_{2d-i} = qᵈ / Aᵢ`, invariance under
automorphisms of `ℂ`, integrality and the Riemann hypothesis `‖α‖ = √(qⁱ)`. -/
theorem IsWeilFactorization.inverseRoots_spec {q d : ℕ} (hq : 0 < q) {Z : PowerSeries ℚ}
    {P : Fin (2 * d + 1) → ℤ[X]} (hfact : IsWeilFactorization q d Z P)
    (hfe : WeilFunctionalEquation q d P) (hrh : WeilRiemannHypothesis q d P) :
    weilInverseRoots P 0 = {1} ∧
      ∀ i ≤ 2 * d, weilInverseRoots P (2 * d - i) =
          (weilInverseRoots P i).map ((q : ℂ) ^ d / ·) ∧
        (∀ φ : ℂ ≃+* ℂ, (weilInverseRoots P i).map φ = weilInverseRoots P i) ∧
        ∀ α ∈ weilInverseRoots P i, _root_.IsIntegral ℤ α ∧ ‖α‖ = √((q : ℝ) ^ i) := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [weilInverseRoots_of_lt P (by omega)]
    have h0 : P ⟨0, by omega⟩ = 1 - X := hfact.apply_zero
    rw [h0, Polynomial.map_sub, Polynomial.map_one, map_X, ← neg_sub, roots_neg,
      ← C_1, roots_X_sub_C]
    simp
  have hi' : i < 2 * d + 1 := by omega
  rw [weilInverseRoots_of_lt P hi']
  refine ⟨?_, fun φ ↦ ?_, fun α hα ↦ ?_⟩
  · rw [weilInverseRoots_of_lt P (by omega)]
    have h := hfe ⟨i, hi'⟩
    have hrev : (⟨i, hi'⟩ : Fin (2 * d + 1)).rev = ⟨2 * d - i, by omega⟩ := by
      ext; simp only [Fin.val_rev]; omega
    rw [hrev] at h
    rw [h, Multiset.map_map, Multiset.map_map]
    congr 1
    ext z
    simp [div_eq_mul_inv]
  · rw [Multiset.map_map]
    conv_rhs => rw [← map_roots_map_intCast_ringEquiv (P ⟨i, hi'⟩) φ, Multiset.map_map]
    congr 1
    ext z
    simp
  · obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hα
    exact ⟨isIntegral_inv_of_mem_roots_map_intCast (hfact.coeff_zero_eq_one _) hz,
      norm_inv_eq_sqrt hq i (hrh ⟨i, hi'⟩ z hz)⟩

namespace Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The point count as an alternating sum of power sums of inverse roots**, indexed by
`i ≤ 2 d`. -/
theorem Hom.pointCount_eq_sum_inverseRoots (f : X.Hom (Spec (.of k))) {q d : ℕ}
    {P : Fin (2 * d + 1) → ℤ[X]} (hfact : IsWeilFactorization q d f.zetaSeries P)
    {n : ℕ} (hn : n ≠ 0) :
    (f.pointCount n : ℂ) = ∑ i ∈ Finset.Iic (2 * d),
      (-1) ^ i * ((weilInverseRoots P i).map (· ^ n)).sum := by
  rw [f.pointCount_eq_sum_roots hfact hn, ← Nat.range_succ_eq_Iic,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [weilInverseRoots_of_lt P i.2, Multiset.map_map]
  rfl

/-- An `F`-point of `X` over a finite extension `E` of `k` is the same as a morphism
`Spec E ⟶ X` in the category of schemes over `Spec k`. -/
def Hom.overHomEquivFieldPoints (Y : Over (Spec (.of k))) (E : Type u) [Field E]
    [Algebra k E] :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E))) ⟶ Y) ≃
      Hom.fieldPoints (X := Y.left) (k := k) Y.hom E where
  toFun g := ⟨g.left, Over.w g⟩
  invFun g := Over.homMk g.1 g.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Over a finite field `k`, the number of points of `X` over a finite extension `E` of `k` is
the point count `N_n` for `n = [E : k]`. -/
theorem Hom.nat_card_fieldPoints_eq_pointCount [Finite k] (f : X.Hom (Spec (.of k)))
    (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E] :
    Nat.card (f.fieldPoints E) = f.pointCount (Module.finrank k E) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Finite E := Module.finite_of_finite k
  have : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Nat.card k ^ Module.finrank k E := by
    rw [Module.card_eq_pow_finrank (K := k) (V := E), Nat.card_eq_fintype_card]
  have : IsSplittingField k E
      (Polynomial.X ^ Nat.card k ^ Module.finrank k E - Polynomial.X) :=
    hcard ▸ FiniteField.isSplittingField_sub E k
  exact f.nat_card_fieldPoints_congr (IsSplittingField.algEquiv E _)

end Scheme

end AlgebraicGeometry

end


open CategoryTheory AlgebraicGeometry

namespace LeanEval.AlgebraicGeometry.WeilConjectures

/-- The **Weil conjectures** in terms of point counts: if `X` is a smooth complete
algebraic variety (geometrically irreducible) over a finite field `F` of dimension `d`,
then there exists multisets `Aᵢ` of Frobenius eigenvalues (which are algebraic integers)
such that for the finite extension `E / F` of degree `m`, we have
`#X(E) = ∑_{0 ≤ i ≤ 2d} (-1)ⁱ ∑_{α ∈ Aᵢ} αᵐ` (rationality of the zeta series).
Moreover, the multisets satisfy `A₀ = {1}`, the Poincaré duality (functional equation)
`A_{2d-i} = #Fᵈ / Aᵢ`, the "Riemann hypothesis" `|α| = #F^{i/2}` for all `α ∈ Aᵢ`,
and are invariant under all automorphisms of ℂ.

This statement does not include the identities between sizes of the multisets and
the Betti numbers of a complex variety defined over a number field whose reduction
modulo a prime ideal is `X`.

The Riemann hypothesis was first proved by Deligne while the rest were already established
by Grothendieck (with Artin, Verdier and earlier work of Dwork) using the theory of ℓ-adic
cohomology. -/
theorem weil_conjectures (F : Type*) [Finite F] [Field F]
    (X : Over (Spec (.of F))) [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ A : ℕ → Multiset ℂ, A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map (Nat.card F ^ d / · : ℂ → ℂ) ∧
        (∀ φ : ℂ ≃+* ℂ, (A i).map φ = A i) ∧
        ∀ α ∈ A i, IsIntegral ℤ α ∧ ‖α‖ = √(Nat.card F ^ i)) ∧
      ∀ (E : Type _) [Field E] [Algebra F E] [FiniteDimensional F E],
        Nat.card (.mk (Spec.map <| CommRingCat.ofHom <| algebraMap F E) ⟶ X) =
        ∑ i ∈ Finset.Iic (2 * d), (-1) ^ i * ((A i).map (· ^ Module.finrank F E)).sum := by
  let f : X.left ⟶ Spec (.of F) := X.hom
  have : SmoothOfRelativeDimension d f := ‹_›
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : IsProper f := ‹_›
  have : GeometricallyIrreducible f := ‹_›
  have : GeometricallyIntegral f := .of_smooth_of_geometricallyIrreducible f
  obtain ⟨P, hfact, hfe, hrh⟩ := Scheme.weil_conjectures f d
  obtain ⟨h0, hi⟩ := hfact.inverseRoots_spec Nat.card_pos hfe hrh
  refine ⟨weilInverseRoots P, h0, fun i hi' ↦ ?_, fun E _ _ _ ↦ ?_⟩
  · simpa using hi i hi'
  · rw [Nat.card_congr (Scheme.Hom.overHomEquivFieldPoints X E),
      Scheme.Hom.nat_card_fieldPoints_eq_pointCount f E]
    exact f.pointCount_eq_sum_inverseRoots hfact Module.finrank_pos.ne'

end LeanEval.AlgebraicGeometry.WeilConjectures
