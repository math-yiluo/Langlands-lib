/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement
public import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
public import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SegreTwist
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Ample invertible modules and the Hilbert degree

An `𝒪_X`-module is *very ample* relative to `f : X ⟶ S` if it is the pullback of `𝒪(1)` along
a closed immersion of `X` into a projective space `ℙ(n; S)` over `S`; it is then invertible. An
invertible module on a `K`-scheme is *ample* if some positive tensor power of it is very ample;
since very ample modules come from *closed* immersions into projective space, this is ampleness
on a projective `K`-scheme (see the warning in the docstring of `AlgebraicGeometry.IsAmple`).
For an ample invertible module `M` on a proper `K`-scheme `X` of dimension `g`, the function
`m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most `g`, and the *degree of `X` with
respect to `M`* is `g!` times its leading coefficient.

`AlgebraicGeometry.IsVeryAmple` and `AlgebraicGeometry.IsAmple` are built on the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist`. The degree `AlgebraicGeometry.Scheme.Hom.degree` is
the `g`-th forward difference `fwdDiff` at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar`; it is `g!` times the
leading coefficient whenever that function is a numerical polynomial of degree at most `g`
(`Polynomial.fwdDiff_iter_degree_eq_factorial`).

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample modules.
- `AlgebraicGeometry.Scheme.Hom.hilbertFunction`: the Hilbert function `m ↦ χ(X, M^{⊗ m})`.
- `AlgebraicGeometry.Scheme.Hom.degree`: the degree of a proper scheme with respect to an ample
  invertible module.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_polynomial_hilbertFunction`: the Hilbert function of an
  ample invertible module on a proper scheme is a polynomial of degree at most `dim X`.
- `AlgebraicGeometry.Scheme.Hom.degree_eq_factorial_mul_coeff`: the degree is `g!` times the
  coefficient of `m^g` of the Hilbert polynomial.
- `AlgebraicGeometry.Scheme.Hom.degree_tensorPow`: `deg_{M^{⊗ k}}(X) = k^g deg_M(X)`.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_nonempty`: an ample invertible module
  on a nonempty proper scheme has positive degree.
- `AlgebraicGeometry.Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one`: in dimension
  one the degree is the cohomological degree `χ(M) - χ(𝒪_X)`.
- `AlgebraicGeometry.IsVeryAmple.isInvertible`: a very ample module is invertible.
- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_H`: the cohomology of an invertible module
  on a proper scheme over a field is finite-dimensional.
- `AlgebraicGeometry.Scheme.Modules.degree_eq_sum_of_pairwise_disjoint`: the degree is additive
  over a finite disjoint union of open subschemes.
- `AlgebraicGeometry.Scheme.Modules.degree_eq_zero_of_topologicalKrullDim_le_zero`: an
  invertible module on a connected noetherian scheme of dimension `0` has degree `0`.
- `AlgebraicGeometry.IsAmple.pullback`: the restriction of an ample module to a closed subscheme
  is ample.
- `AlgebraicGeometry.IsAmple.pullback_of_field` and `AlgebraicGeometry.IsVeryAmple.of_pullback`:
  ampleness is stable under field extension, and very ampleness descends along it.
- `AlgebraicGeometry.isAffine_compl_of_isAmple_dual_toModules`: the complement of an effective
  Cartier divisor with ample line bundle is affine.
- `AlgebraicGeometry.IsAmple.tensorPow`: positive tensor powers of an ample module are ample.
- `AlgebraicGeometry.IsVeryAmple.tensorObj`, `AlgebraicGeometry.IsAmple.tensorObj`: tensor
  products of very ample, respectively ample, modules are very ample, respectively ample.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace`: an ample invertible
  module on a connected proper curve has positive degree.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`: an ample invertible module on a proper
  curve has positive degree.
- `AlgebraicGeometry.IsAmple.isEmpty_iso_unit`: an ample invertible module on a proper curve is
  not trivial.
- `AlgebraicGeometry.IsAmple.isEmpty_tensorPow_iso_unit`: no positive tensor power of an ample
  invertible module on a proper curve is trivial.
- `AlgebraicGeometry.Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow`: twisting the
  Hilbert function by a coherent module of generic rank `r` multiplies the degree by `r`.
- `AlgebraicGeometry.Scheme.Hom.degree_pullback`: the degree multiplies by the degree of the
  morphism under pullback along a finite surjective morphism.

## Implementation details

The degree of a pullback is computed via the projection formula
`χ(X, (g^* M)^{⊗ m}) = χ(Y, g_* 𝒪_X ⊗ M^{⊗ m})`, where `g_* 𝒪_X` is coherent of generic rank
`d`; the leading coefficients are then compared by
`AlgebraicGeometry.Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow`.

## References

* Stacks Project, Tags 0BEV, 0BEX and 0B5X
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Function MonoidalCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- The Hilbert function `m ↦ χ(X, M^{⊗ m})` of an `𝒪_X`-module `M` on a `K`-scheme `X`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` over `K`. -/
noncomputable def Scheme.Hom.hilbertFunction (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℕ → ℤ :=
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  fun m ↦ Scheme.Modules.eulerChar K (M.tensorPow m)

open scoped fwdDiff in
/-- The degree of a `K`-scheme `X` of dimension `g` with respect to an `𝒪_X`-module `M`: the `g`-th
forward difference at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`. When the Hilbert
function is a numerical polynomial of degree at most `g`, as it is for `X` proper and `M` ample
invertible, this equals `g!` times its coefficient of `m^g`. Here `g` is the topological Krull
dimension of `X`, read as `0` if `X` is empty or infinite-dimensional.

The value is meaningful only for `f` proper and `M` coherent: otherwise the Euler
characteristics involved may be junk values. -/
noncomputable def Scheme.Hom.degree (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ :=
  Δ_[1] ^[((topologicalKrullDim X).unbotD 0).toNat] (f.hilbertFunction M) 0

/-- The degree as an explicit alternating sum of Euler characteristics:
`∑_{i=0}^{g} (-1)^(g-i) (g choose i) χ(X, M^{⊗ i})`. -/
lemma Scheme.Hom.degree_eq_sum (f : X ⟶ Spec (.of K)) (M : X.Modules) :
    f.degree M = ∑ i ∈ Finset.range (((topologicalKrullDim X).unbotD 0).toNat + 1),
      ((-1 : ℤ) ^ (((topologicalKrullDim X).unbotD 0).toNat - i) *
        (((topologicalKrullDim X).unbotD 0).toNat.choose i : ℤ)) • f.hilbertFunction M i := by
  rw [degree, fwdDiff_iter_eq_sum_shift]
  simp

/-- On a `K`-scheme of dimension one, the degree with respect to `M` is the cohomological
degree `χ(M) - χ(𝒪_X)` of `AlgebraicGeometry.Scheme.Modules.degree`. -/
lemma Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one (f : X ⟶ Spec (.of K))
    (h : topologicalKrullDim X = 1) (M : X.Modules) :
    letI : X.Over (Spec (.of K)) := ⟨f⟩
    f.degree M = Scheme.Modules.degree K M := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have hg : ((topologicalKrullDim X).unbotD 0).toNat = 1 := by
    rw [h]
    rfl
  rw [degree, hg, Function.iterate_one, fwdDiff, zero_add, Scheme.Modules.degree]
  simp only [hilbertFunction, Scheme.Modules.tensorPow_zero]
  rw [Scheme.Modules.tensorPow_succ, Scheme.Modules.tensorPow_zero,
    Scheme.Modules.eulerChar_congr K (MonoidalCategory.rightUnitor M)]
  rfl

/-- The Hilbert polynomial.

Let `X` be a proper scheme of dimension `g` over a field `K` and `M` an ample invertible
`𝒪_X`-module. Then `m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most `g`: there is
a polynomial `P` over `ℚ` of degree at most `g` with `P(m) = χ(X, M^{⊗ m})` for all `m`, the
*Hilbert polynomial* of `M` (Stacks, Tag 0BEM). -/
theorem Scheme.Hom.exists_polynomial_hilbertFunction (f : X ⟶ Spec (.of K)) [IsProper f]
    (M : X.Modules) (hM : IsAmple f M) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ ((topologicalKrullDim X).unbotD 0).toNat ∧
      ∀ m : ℕ, P.eval (m : ℚ) = f.hilbertFunction M m := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of K)) := ‹IsProper f›
  have := hM.isInvertible
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  obtain ⟨P, hP, hP'⟩ := Scheme.Modules.exists_polynomial_eulerChar_tensorObj_tensorPow_of_le K
    hM (𝟙_ X.Modules) (Scheme.Modules.topologicalKrullDim_le_unbotD_toNat K)
  exact ⟨P, hP, fun m ↦ (hP' m).trans (by
    rw [Scheme.Modules.eulerChar_congr K (λ_ _)]
    rfl)⟩

open scoped fwdDiff in
/-- The Hilbert degree of an ample line bundle.

If the Hilbert function `m ↦ χ(X, M^{⊗ m})` is given by a polynomial `P` of degree at most
`g = dim X`, then the degree of `X` with respect to `M` is `g!` times the coefficient of `m^g`
in `P`. -/
theorem Scheme.Hom.degree_eq_factorial_mul_coeff (f : X ⟶ Spec (.of K)) (M : X.Modules)
    {P : Polynomial ℚ} (hP : P.natDegree ≤ ((topologicalKrullDim X).unbotD 0).toNat)
    (hPM : ∀ m : ℕ, P.eval (m : ℚ) = f.hilbertFunction M m) :
    (f.degree M : ℚ) = ((topologicalKrullDim X).unbotD 0).toNat.factorial *
      P.coeff ((topologicalKrullDim X).unbotD 0).toNat := by
  rw [degree]
  generalize ((topologicalKrullDim X).unbotD 0).toNat = g at hP ⊢
  have h : ((Δ_[1] ^[g] (f.hilbertFunction M) 0 : ℤ) : ℚ) = Δ_[1] ^[g] P.eval 0 := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [← hPM]
  rw [h]
  rcases hP.lt_or_eq with hlt | rfl
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp
  · rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    simp [mul_comm]

/-- Ample modules and the Hilbert degree.

Let `X` be a proper scheme of dimension `g` over a field `K` and `M` an ample invertible
`𝒪_X`-module. Then `m ↦ χ(X, M^{⊗ m})` is given by a polynomial `P` of degree at most `g`, and
the degree of `X` with respect to `M` is `g!` times the leading coefficient of `P`, its
coefficient of `m^g`. -/
theorem Scheme.Hom.exists_polynomial_degree_eq_factorial_mul_coeff (f : X ⟶ Spec (.of K))
    [IsProper f] (M : X.Modules) (hM : IsAmple f M) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ ((topologicalKrullDim X).unbotD 0).toNat ∧
      (∀ m : ℕ, P.eval (m : ℚ) = f.hilbertFunction M m) ∧
      (f.degree M : ℚ) = ((topologicalKrullDim X).unbotD 0).toNat.factorial *
        P.coeff ((topologicalKrullDim X).unbotD 0).toNat := by
  obtain ⟨P, hP, hPM⟩ := f.exists_polynomial_hilbertFunction M hM
  exact ⟨P, hP, hPM, f.degree_eq_factorial_mul_coeff M hP hPM⟩

/-- The Hilbert function only depends on the isomorphism class of the module. -/
lemma Scheme.Hom.hilbertFunction_congr (f : X ⟶ Spec (.of K)) {M N : X.Modules} (e : M ≅ N) :
    f.hilbertFunction M = f.hilbertFunction N := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have h (m : ℕ) : Nonempty (M.tensorPow m ≅ N.tensorPow m) := by
    induction m with
    | zero => exact ⟨Iso.refl _⟩
    | succ m ih => exact ⟨e ⊗ᵢ ih.some⟩
  funext m
  exact Scheme.Modules.eulerChar_congr K (h m).some

/-- The degree only depends on the isomorphism class of the module. -/
lemma Scheme.Hom.degree_congr (f : X ⟶ Spec (.of K)) {M N : X.Modules} (e : M ≅ N) :
    f.degree M = f.degree N := by
  rw [degree, degree, f.hilbertFunction_congr e]

/-- The Hilbert function of `M^{⊗ k}` is `m ↦ χ(X, M^{⊗ k m})`. -/
lemma Scheme.Hom.hilbertFunction_tensorPow (f : X ⟶ Spec (.of K)) (M : X.Modules) (k m : ℕ) :
    f.hilbertFunction (M.tensorPow k) m = f.hilbertFunction M (k * m) := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  exact Scheme.Modules.eulerChar_congr K (M.tensorPowMulIso k m).symm

/-- **The degree of a tensor power.** Let `X` be a proper scheme of dimension `g` over `K` and
`M` an ample invertible `𝒪_X`-module. Then `deg_{M^{⊗ k}}(X) = k^g deg_M(X)`. -/
theorem Scheme.Hom.degree_tensorPow (f : X ⟶ Spec (.of K)) [IsProper f] (M : X.Modules)
    (hM : IsAmple f M) (k : ℕ) :
    f.degree (M.tensorPow k) = k ^ ((topologicalKrullDim X).unbotD 0).toNat * f.degree M := by
  have hcoeff (P : Polynomial ℚ) (n : ℕ) :
      (P.comp (Polynomial.C (k : ℚ) * Polynomial.X)).coeff n = (k : ℚ) ^ n * P.coeff n := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
    | monomial m a =>
      simp only [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
        ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
      split_ifs with h₁ h₂ h₂
      · subst h₁; ring
      · exact absurd h₁.symm h₂
      · exact absurd h₂.symm h₁
      · simp
  obtain ⟨P, hP, hPM, hdeg⟩ := f.exists_polynomial_degree_eq_factorial_mul_coeff M hM
  set g := ((topologicalKrullDim X).unbotD 0).toNat
  have hQ : (P.comp (Polynomial.C (k : ℚ) * Polynomial.X)).natDegree ≤ g :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun n hn ↦ by
      rw [hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hn), mul_zero]
  have hQM (m : ℕ) : (P.comp (Polynomial.C (k : ℚ) * Polynomial.X)).eval (m : ℚ) =
      f.hilbertFunction (M.tensorPow k) m := by
    rw [f.hilbertFunction_tensorPow, ← hPM]
    simp
  have := f.degree_eq_factorial_mul_coeff (M.tensorPow k) hQ hQM
  rw [hcoeff] at this
  have h : (f.degree (M.tensorPow k) : ℚ) = (k : ℚ) ^ g * f.degree M := by
    rw [this, hdeg]
    ring
  exact_mod_cast h

namespace Scheme.Modules

section Additivity

variable (K) [X.Over (Spec (.of K))]

/-- **Finiteness of cohomology.** The cohomology of an invertible module on a proper scheme over
a field `K` is finite-dimensional over `K`. -/
instance finiteDimensional_H [IsProper (X ↘ Spec (.of K))] (M : X.Modules) [M.IsInvertible]
    (q : ℕ) : FiniteDimensional K (M.H q) :=
  have := IsInvertible.sheafOfModules_isInvertible M
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree M
  have := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation M
  finiteDimensional_H_of_isProper M q

/-- **The degree is additive over a finite disjoint union.** If a noetherian scheme `X` of
finite dimension is the disjoint union of finitely many open subschemes `U i`, then
`deg M = ∑ᵢ deg (M|_{U i})`, provided the cohomology of `M` and `𝒪_X` is finite-dimensional. -/
theorem degree_eq_sum_of_pairwise_disjoint [IsNoetherian X] {n : ℕ}
    (hn : topologicalKrullDim X ≤ n) {ι : Type*}
    [Fintype ι] (U : ι → X.Opens) (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤)
    (M : X.Modules) [∀ q, FiniteDimensional K (M.H q)]
    [∀ q, FiniteDimensional K ((𝟙_ X.Modules).H q)] :
    M.degree K = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).degree K := by
  let (i : ι) : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
  simp only [degree, Finset.sum_sub_distrib]
  rw [eulerChar_eq_sum_of_pairwise_disjoint K hn U hU hcover M]
  congr 1
  exact (eulerChar_eq_sum_of_pairwise_disjoint K hn U hU hcover (𝟙_ X.Modules)).trans
    (Finset.sum_congr rfl fun i _ ↦ eulerChar_congr K (pullbackObjUnitIso _))

/-- **The degree is additive over a finite disjoint union**, for a quasi-coherent module on a
quasi-compact separated scheme. This is
`AlgebraicGeometry.Scheme.Modules.degree_eq_sum_of_pairwise_disjoint` without the appeal to
Grothendieck vanishing. -/
theorem degree_eq_sum_of_pairwise_disjoint_of_isQuasicoherent [CompactSpace X]
    [IsSeparated (terminal.from X)] {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] [∀ q, FiniteDimensional K (M.H q)]
    [∀ q, FiniteDimensional K ((𝟙_ X.Modules).H q)] :
    M.degree K = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).degree K := by
  let (i : ι) : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
  simp only [degree, Finset.sum_sub_distrib]
  rw [eulerChar_eq_sum_of_pairwise_disjoint_of_isQuasicoherent K U hU hcover M]
  congr 1
  exact (eulerChar_eq_sum_of_pairwise_disjoint_of_isQuasicoherent K U hU hcover
    (𝟙_ X.Modules)).trans (Finset.sum_congr rfl fun i _ ↦ eulerChar_congr K (pullbackObjUnitIso _))

/-- On a connected locally noetherian `K`-scheme of dimension `0`, every invertible module has
degree `0`: the scheme is artinian, hence discrete, hence a single point, on which every
invertible module is trivial. -/
theorem degree_eq_zero_of_topologicalKrullDim_le_zero [IsLocallyNoetherian X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X ≤ 0) (L : X.Modules) [L.IsInvertible] : L.degree K = 0 := by
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have : Subsingleton X := Set.subsingleton_univ_iff.mp isPreconnected_univ.subsingleton
  obtain ⟨e⟩ := IsInvertible.nonempty_iso_unit (Classical.arbitrary X) L
  rw [degree_congr K e, degree_unit]

end Additivity

end Scheme.Modules

/-- **Very ampleness descends along a field extension.** Let `X` be proper over a field `k`, let
`M` be an invertible `𝒪_X`-module and `K/k` a field extension such that `M_K` is very ample on
`X_K`. Then `M` is very ample. The closed immersion `X_K ⟶ ℙ(n; K)` is given by finitely many
sections of `M_K`, which lie in the `K`-span of finitely many sections of `M`, since
`H⁰(X_K, M_K) = H⁰(X, M) ⊗_k K`; these define a morphism `X ⟶ ℙ(V)` whose base change to `K`
is a closed immersion, hence which is a closed immersion by fpqc descent. -/
theorem IsVeryAmple.of_pullback {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (K : Type u) [Field K] [Algebra k K] (M : X.Modules) [M.IsInvertible]
    (h : IsVeryAmple (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M)) :
    IsVeryAmple f M := by
  classical
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set φ := pullback.fst f g
  set p := pullback.snd f g
  set MK := (Scheme.Modules.pullback φ).obj M
  obtain ⟨n, i', hn, hi', hi'f, ⟨e⟩⟩ := h
  have := Fintype.ofFinite n
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible M
  have hsurj : AlgebraicGeometry.Surjective g := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  -- the sections `s' l = i'^* T_l` of `M_K` defining `i'`
  have hle : (⊤ : (Limits.pullback f g).Opens) ≤ i' ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  let s' (l : n) : Γ(MK, ⊤) := MK.presheaf.map (homOfLE hle).op
    (e.hom.app _ (Scheme.Modules.pullbackSection i' (ProjectiveSpace.twistOneSection n _ l)))
  have hs' (l : n) : e.hom.app _
      (Scheme.Modules.pullbackSection i' (ProjectiveSpace.twistOneSection n _ l)) =
      MK.presheaf.map (homOfLE (le_top : i' ⁻¹ᵁ ⊤ ≤ ⊤)).op (s' l) := by
    rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE, Scheme.Modules.presheaf_map_id_apply]
  -- they are `K`-linear combinations of pullbacks of sections `u r` of `M`
  choose N c t ht using fun l ↦
    Scheme.Modules.exists_eq_sum_smul_pullbackTopSection f (K := K) M (s' l)
  let m : Type u := Σ l : n, ULift.{u} (Fin (N l))
  let u : m → Γ(M, ⊤) := fun r ↦ t r.1 r.2.down
  let C : n → m → Γ(Spec (.of K), ⊤) := fun l r ↦
    if r.1 = l then (Scheme.ΓSpecIso (.of K)).inv (c r.1 r.2.down) else 0
  have hv (l : n) : s' l = ∑ r, p.appTop (C l r) • Scheme.Modules.pullbackTopSection φ (u r) := by
    rw [ht l, Fintype.sum_sigma, Finset.sum_eq_single l]
    · exact Fintype.sum_equiv Equiv.ulift.symm _ _ fun q ↦ by simp [C, u]; rfl
    · intro l' _ hl'
      simp [C, hl']
    · simp
  -- the `u r` generate `M`, since the `s' l` generate `M_K`
  have hU : ⨆ r, Scheme.Modules.generatingLocus (u r) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨y, rfl⟩ := φ.surjective x
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp
      ((ProjectiveSpace.iSup_standardOpen n _).ge (Set.mem_univ (i' y)))
    have hgen : Scheme.Modules.GeneratesAt (s' l) y := by
      rw [← Scheme.Modules.mem_generatingLocus,
        ProjectiveSpace.generatingLocus_eq_preimage_standardOpen e.hom hs' l]
      exact hl
    rw [hv l] at hgen
    obtain ⟨r, -, hr⟩ :=
      Scheme.Modules.exists_generatesAt_of_generatesAt_sum φ Finset.univ _ u hgen
    exact Opens.mem_iSup.mpr ⟨r, hr⟩
  -- the morphism `j: X ⟶ ℙ(m; k)` given by the `u r`
  obtain ⟨j, hj, εj, hεj_iso, hεj⟩ := ProjectiveSpace.exists_hom_twistRestrict u
    (fun r ↦ Scheme.Modules.generatingLocus (u r))
    (fun r ↦ Scheme.Modules.isFreeGenerator_generatingLocus (u r)) f hU
  -- the morphism `ψ: X_K ⟶ ℙ(m; K)` given by the `φ^* u r`
  have hU' : ⨆ r, Scheme.Modules.generatingLocus
      (Scheme.Modules.pullbackTopSection φ (u r)) = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    obtain ⟨r, hr⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ (φ y)))
    exact Opens.mem_iSup.mpr ⟨r, Scheme.Modules.preimage_generatingLocus_le φ (u r) hr⟩
  obtain ⟨ψ, hψ, εψ, hεψ_iso, hεψ⟩ := ProjectiveSpace.exists_hom_twistRestrict
    (fun r ↦ Scheme.Modules.pullbackTopSection φ (u r))
    (fun r ↦ Scheme.Modules.generatingLocus (Scheme.Modules.pullbackTopSection φ (u r)))
    (fun r ↦ Scheme.Modules.isFreeGenerator_generatingLocus _) p hU'
  -- `ψ` is the base change of `j`
  have hψj : ψ ≫ ProjectiveSpace.map m g = φ ≫ j :=
    ProjectiveSpace.map_comp_eq_of_pullbackTopSection g φ εj hεj εψ hεψ
      (by rw [reassoc_of% hψ, hj, pullback.condition])
  have hpb : IsPullback ψ φ (ProjectiveSpace.map m g) j :=
    IsPullback.of_right (h₂₂ := ℙ(m; Spec (.of k)) ↘ Spec (.of k))
      (h₁₂ := ℙ(m; Spec (.of K)) ↘ Spec (.of K)) (v₁₃ := g)
      (by rw [hψ, hj]; exact (IsPullback.of_hasPullback f g).flip) hψj
      (ProjectiveSpace.isPullback_map m g).flip
  -- `ψ` is a monomorphism, since `i'` is, hence a closed immersion
  have : Mono i' := ((IsClosedImmersion.iff_isFinite_and_mono i').mp hi').2
  have hmono : Mono ψ := ProjectiveSpace.mono_of_eq_sum_smul εψ hεψ e.hom hs' hψ hv hi'f
  have : LocallyOfFiniteType (ψ ≫ ℙ(m; Spec (.of K)) ↘ Spec (.of K)) := by
    rw [hψ]
    infer_instance
  have : LocallyOfFiniteType ψ := locallyOfFiniteType_of_comp ψ (ℙ(m; Spec (.of K)) ↘ Spec (.of K))
  have : IsProper (ψ ≫ ℙ(m; Spec (.of K)) ↘ Spec (.of K)) := by
    rw [hψ]
    infer_instance
  have : IsProper ψ := IsProper.of_comp ψ (ℙ(m; Spec (.of K)) ↘ Spec (.of K))
  have : IsFinite ψ := IsFinite.of_isProper_of_locallyQuasiFinite ψ
  have hψci : IsClosedImmersion ψ :=
    (IsClosedImmersion.iff_isFinite_and_mono ψ).mpr ⟨inferInstance, hmono⟩
  -- so `j` is a closed immersion by fpqc descent
  have := IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact.{u}
  have hflat : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hQ : (@AlgebraicGeometry.Surjective ⊓ @Flat ⊓ @QuasiCompact :
      MorphismProperty Scheme.{u})
      (ProjectiveSpace.map m g) :=
    ⟨⟨MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map m g).flip hsurj,
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map m g).flip hflat⟩,
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map m g).flip inferInstance⟩
  have hjci : IsClosedImmersion j := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsClosedImmersion) hpb hQ hψci
  exact ⟨m, j, inferInstance, hjci, hj, ⟨asIso εj⟩⟩

open scoped Scheme.Modules in
/-- **The complement of an ample effective divisor is affine.** Let `X` be proper over a field
`k` and `D ⊆ X` an effective Cartier divisor, with invertible ideal sheaf `J = 𝒪_X(-D)`, whose
line bundle `𝒪_X(D) = J.toModulesᵛ` is ample. Then `X \ D` is affine, where the open
complement of `D` is presented by an open immersion `j` whose range is the complement of the
support of `J`. -/
theorem isAffine_compl_of_isAmple_dual_toModules {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hample : IsAmple f J.toModulesᵛ) {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j.base = (J.support : Set X)ᶜ) :
    IsAffine V := by
  have := hJ.isInvertible_dual_toModules
  obtain ⟨-, m, hm, n, i, hn, hi, -, ⟨e⟩⟩ := hample
  obtain ⟨s, hs⟩ := hJ.exists_zeroLocus_eq
  let L := ProjectiveSpace.twistRestrict i 1
  have : L.IsInvertible := Scheme.Modules.IsInvertible.of_iso e.symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible _
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ (ℙ(n; Spec (.of k))).Modules) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible _
  -- The pullbacks `x l` of the coordinate sections, with non-vanishing loci `i⁻¹ D₊(T_l)`.
  let x (l : n) : 𝟙_ X.Modules ⟶ L := (Scheme.Modules.pullbackObjUnitIso i).inv ≫
    (Scheme.Modules.pullback i).map (ProjectiveSpace.coordinateSection n _ l)
  have hx (l : n) : (Scheme.Modules.Hom.zeroLocus (x l)).support.compl =
      i ⁻¹ᵁ ProjectiveSpace.standardOpen n _ l := by
    have h₁ : (x l).zeroLocus =
        ((Scheme.Modules.pullback i).map (ProjectiveSpace.coordinateSection n _ l)).zeroLocus :=
      Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
        (Arrow.isoMk (Scheme.Modules.pullbackObjUnitIso _).symm (Iso.refl _)
          (Category.comp_id _).symm)
    rw [h₁, ← Scheme.Modules.Hom.comap_zeroLocus,
      ← ProjectiveSpace.compl_support_zeroLocus_coordinateSection]
    exact (congrArg TopologicalSpace.Closeds.compl
      (Scheme.IdealSheafData.support_comap _ i)).trans rfl
  -- The `m`-th power `t` of the canonical section of `𝒪_X(D)`, with non-vanishing locus `X \ D`.
  let t : 𝟙_ X.Modules ⟶ L := Scheme.Modules.tensorPowSection s m ≫ e.inv
  have ht : (Scheme.Modules.Hom.zeroLocus t).support.compl = J.support.compl := by
    have h₁ : (Scheme.Modules.tensorPowSection s m).zeroLocus = t.zeroLocus :=
      Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
        (Arrow.isoMk (Iso.refl _) e.symm (by simp [t]))
    rw [← h₁, Scheme.Modules.compl_support_zeroLocus_tensorPowSection _ s hm, hs]
  have hU := Scheme.Modules.isAffineOpen_compl_support_zeroLocus f L x
    (fun l ↦ hx l ▸ (ProjectiveSpace.isAffineOpen_standardOpen n _ l).preimage i)
    (eq_top_iff.mpr fun p _ ↦ by
      obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((ProjectiveSpace.iSup_standardOpen n (Spec (.of k))).ge (Set.mem_univ (i p)))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, by rw [hx]; exact hl⟩) t
  have hr : j.opensRange = J.support.compl := by
    ext1
    exact hj
  rw [ht, ← hr] at hU
  have : IsAffine j.opensRange.toScheme := hU
  exact IsAffine.of_isIso j.isoOpensRange.hom

/-- **An ample module has positive degree.** Let `X` be a nonempty proper scheme over a field
`K` and `M` an ample invertible `𝒪_X`-module. Then the degree of `X` with respect to `M` is
positive. -/
@[stacks 0BEV]
theorem Scheme.Hom.degree_pos_of_isAmple_of_nonempty (f : X ⟶ Spec (.of K)) [IsProper f]
    [Nonempty X] (M : X.Modules) (hample : IsAmple f M) : 0 < f.degree M := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of K)) := ‹IsProper f›
  obtain ⟨P, hnat, hlc, hP⟩ :=
    Scheme.Modules.exists_polynomial_natDegree_eq_leadingCoeff_pos K hample
  have hPM (m : ℕ) : P.eval (m : ℚ) = f.hilbertFunction M m := by
    rw [hP m, Scheme.Modules.eulerChar_congr K (λ_ _)]
    rfl
  have h := f.degree_eq_factorial_mul_coeff M hnat.le hPM
  rw [← hnat] at h
  have : (0 : ℚ) < f.degree M := by
    rw [h]
    exact mul_pos (by exact_mod_cast Nat.factorial_pos _) hlc
  exact_mod_cast this

/-- **An ample module on a connected proper curve has positive degree.** Let `K` be
algebraically closed, `X` a connected proper curve over `K` and `L` an ample invertible
`𝒪_X`-module. Then `deg L = χ(L) - χ(𝒪_X) > 0`. -/
@[stacks 0B5X]
theorem Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [IsProper f] [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (L : X.Modules) (hample : IsAmple f L) : 0 < f.degree L := by
  -- the dimension hypothesis is not needed
  have _ := hdim
  exact f.degree_pos_of_isAmple_of_nonempty L hample

/-- **Ample modules on proper curves have positive degree.** Let `K` be algebraically closed,
`C` a proper curve over `K` of dimension one (possibly disconnected) and `L` an ample invertible
`𝒪_C`-module. Then `deg L > 0`. -/
theorem Scheme.Hom.degree_pos_of_isAmple [IsAlgClosed K] (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules) (hample : IsAmple f L) :
    0 < f.degree L := by
  have := hample.isInvertible
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of K)) := ‹IsProper f›
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have : Fintype (ConnectedComponents X) := Fintype.ofFinite _
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  -- The connected components `U c` of `X`, open and closed in `X`.
  let U (c : ConnectedComponents X) : X.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {c}, (isOpen_discrete {c}).preimage
      ConnectedComponents.continuous_coe⟩
  have hU : _root_.Pairwise (Disjoint on U) := fun c d hcd ↦
    Opens.coe_disjoint.mp ((Set.disjoint_singleton.mpr hcd).preimage ConnectedComponents.mk)
  have hcover : ⨆ c, U c = ⊤ := eq_top_iff.mpr fun x _ ↦
    Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  let (c : ConnectedComponents X) : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ f⟩
  have hdimU (c : ConnectedComponents X) :
      topologicalKrullDim (U c) = 1 ∨ topologicalKrullDim (U c) ≤ 0 := by
    rcases (hdim ▸ topologicalKrullDim_subspace_le X (U c)).lt_or_eq with h | h
    · exact Or.inr (Order.le_of_lt_succ h)
    · exact Or.inl h
  -- Each component contributes a nonnegative degree, positive if it has dimension `1`.
  have hdeg (c : ConnectedComponents X) :
      0 ≤ ((Scheme.Modules.pullback (U c).ι).obj L).degree K ∧
      (topologicalKrullDim (U c) = 1 →
        0 < ((Scheme.Modules.pullback (U c).ι).obj L).degree K) := by
    have : ConnectedSpace (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      have : (U x : Set X) = connectedComponent x := connectedComponents_preimage_singleton
      exact isConnected_iff_connectedSpace.mp (this ▸ isConnected_connectedComponent)
    have hclosed : IsClosed (U c : Set X) :=
      (isClosed_discrete {c}).preimage ConnectedComponents.continuous_coe
    have : IsClosedImmersion (U c).ι := .of_isPreimmersion _ (by simpa using hclosed)
    have hpos (h1 : topologicalKrullDim (U c) = 1) :
        0 < ((Scheme.Modules.pullback (U c).ι).obj L).degree K := by
      have := ((U c).ι ≫ f).degree_pos_of_isAmple_of_connectedSpace h1 _ (hample.pullback _)
      rwa [degree_eq_degree_of_topologicalKrullDim_eq_one _ h1] at this
    refine ⟨?_, hpos⟩
    rcases hdimU c with h | h
    · exact (hpos h).le
    · exact (Scheme.Modules.degree_eq_zero_of_topologicalKrullDim_le_zero K h _).ge
  rw [degree_eq_degree_of_topologicalKrullDim_eq_one f hdim,
    Scheme.Modules.degree_eq_sum_of_pairwise_disjoint_of_isQuasicoherent K U hU hcover L]
  refine Finset.sum_pos' (fun c _ ↦ (hdeg c).1) ?_
  -- Some component has dimension `1`: otherwise every component is discrete, hence so is `X`.
  by_contra! h
  have : DiscreteTopology X := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
    have := IsLocallyArtinian.of_topologicalKrullDim_le_zero
      ((hdimU (ConnectedComponents.mk x)).resolve_left fun h1 ↦
        (h _ (Finset.mem_univ _)).not_gt ((hdeg _).2 h1))
    have hd : DiscreteTopology (U (ConnectedComponents.mk x)) :=
      IsLocallyArtinian.discreteTopology (X := (U (ConnectedComponents.mk x)).toScheme)
    have := (U (ConnectedComponents.mk x)).isOpen.isOpenMap_subtype_val _
      (@isOpen_discrete _ _ hd {(⟨x, rfl⟩ : U (ConnectedComponents.mk x))})
    convert this using 1
    ext y
    constructor
    · rintro rfl
      exact ⟨⟨y, rfl⟩, rfl, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_singleton_iff.mp hz]
      rfl
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at this
  exact absurd this (by decide)

/-- **An ample module on a proper curve is not trivial.** Let `K` be algebraically closed, `X` a
proper curve over `K` and `L` an ample invertible `𝒪_X`-module. Then `L ≇ 𝒪_X`. -/
theorem IsAmple.isEmpty_iso_unit [IsAlgClosed K] {f : X ⟶ Spec (.of K)} [IsProper f]
    (hdim : topologicalKrullDim X = 1) {L : X.Modules} (hL : IsAmple f L) :
    IsEmpty (L ≅ 𝟙_ X.Modules) := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  refine ⟨fun e ↦ ?_⟩
  have := f.degree_pos_of_isAmple hdim L hL
  rw [Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one f hdim,
    Scheme.Modules.degree_congr K e] at this
  exact this.ne' (Scheme.Modules.degree_unit K)

/-- **No positive tensor power of an ample module on a proper curve is trivial.** Let `K` be
algebraically closed, `X` a proper curve over `K` and `L` an ample invertible `𝒪_X`-module. Then
`L^{⊗ k} ≇ 𝒪_X` for `0 < k`. -/
theorem IsAmple.isEmpty_tensorPow_iso_unit [IsAlgClosed K] {f : X ⟶ Spec (.of K)} [IsProper f]
    (hdim : topologicalKrullDim X = 1) {L : X.Modules} (hL : IsAmple f L)
    {k : ℕ} (hk : 0 < k) : IsEmpty (L.tensorPow k ≅ 𝟙_ X.Modules) := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  refine ⟨fun e ↦ ?_⟩
  have := f.degree_pos_of_isAmple hdim _ (hL.tensorPow hk)
  rw [Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one f hdim,
    Scheme.Modules.degree_congr K e] at this
  exact this.ne' (Scheme.Modules.degree_unit K)

open scoped fwdDiff in
/-- **The leading coefficient of a twisted Hilbert function only depends on the generic rank.**
Let `Y` be an integral proper `K`-scheme of dimension `g`, `M` an ample invertible `𝒪_Y`-module
and `E` a coherent `𝒪_Y`-module which is free of rank `r` on a nonempty open subset of `Y`. Then
the `g`-th forward difference at `0` of `m ↦ χ(Y, E ⊗ M^{⊗ m})` is `r` times the degree of `Y`
with respect to `M`. -/
theorem Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [IsProper f] (M : Y.Modules) (hample : IsAmple f M)
    (E : Y.Modules) [E.IsFinitePresentation] {U : Y.Opens} (hU : (U : Set Y).Nonempty) {r : ℕ}
    (e : (Scheme.Modules.pullback U.ι).obj E ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    letI : Y.Over (Spec (.of K)) := ⟨f⟩
    Δ_[1] ^[((topologicalKrullDim Y).unbotD 0).toNat]
      (fun m ↦ Scheme.Modules.eulerChar K (E ⊗ M.tensorPow m)) 0 = r * f.degree M := by
  let : Y.Over (Spec (.of K)) := ⟨f⟩
  have : IsProper (Y ↘ Spec (.of K)) := ‹IsProper f›
  have := hample.isInvertible
  have := Scheme.Modules.isNoetherian_of_isProper K (X := Y)
  have : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) E :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData E).choose.isQuasicoherent
  set g := ((topologicalKrullDim Y).unbotD 0).toNat
  -- a section `t` of `M^{⊗ c}` with `∅ ≠ D(t) ⊆ U`
  set η := genericPoint Y
  have hηU : η ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  let J := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩
  have hηJ : η ∉ (J.support : Set Y) := by simpa [J] using hηU
  obtain ⟨c, hc⟩ := Scheme.Modules.exists_mem_compl_support_zeroLocus_comp_toModulesι
    (Y ↘ Spec (.of K)) hample J hηJ
  obtain ⟨σ, hσ⟩ := hc c le_rfl
  have : SheafOfModules.IsInvertible.{u, u, u} (M.tensorPow c) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible _
  set t := σ ≫ J.toModulesι ▷ M.tensorPow c ≫ (λ_ _).hom
  set V : Y.Opens := (Scheme.Modules.Hom.zeroLocus t).support.compl
  have hVU : V ≤ U := fun y hy ↦ by
    by_contra hyU
    exact Scheme.Modules.not_generatesAt_of_factors J σ (y := y) (by simpa [J] using hyU)
      ((Scheme.Modules.generatesAt_iff_mem_compl_support t y).mpr hy)
  -- `E` and `𝒪_Y^{⊕ r}` agree on `V`
  let I := ULift.{u} (Fin r)
  let ε : (Scheme.Modules.restrictFunctor V.ι).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj E :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
      Scheme.Modules.pullbackFreeIso V.ι I ≪≫
      (Scheme.Modules.pullbackFreeIso (Y.homOfLE hVU) I).symm ≪≫
      (Scheme.Modules.pullback (Y.homOfLE hVU)).mapIso e.symm ≪≫
      (Scheme.Modules.pullbackComp (Y.homOfLE hVU) U.ι).app E ≪≫
      (Scheme.Modules.pullbackCongr (Y.homOfLE_ι hVU)).app E ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app E).symm
  obtain ⟨m, φ, hφ⟩ := Scheme.Modules.exists_hom_free_isIso_restrictFunctor_map f t E ε
  -- kernel and cokernel of `φ` are supported on the proper closed subset `Vᶜ`
  have hK := Scheme.Modules.isZero_restrict_kernel_of_isIso φ V
  have hC := Scheme.Modules.isZero_restrict_cokernel_of_isIso φ V
  have hdim : topologicalKrullDim (((V : Set Y)ᶜ : Set Y)) < g := by
    refine topologicalKrullDim_lt_of_forall_exists_specializes isClosed_univ
      V.isOpen.isClosed_compl (Set.subset_univ _)
      (fun w _ ↦ ⟨η, trivial, genericPoint_specializes w, fun h ↦ h hσ⟩) ?_
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph]
    exact (Scheme.Modules.topologicalKrullDim_le_unbotD_toNat K).trans_lt
      (by exact_mod_cast Nat.lt_succ_self g)
  have := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ Y.Modules)
  have : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf)
      (SheafOfModules.free (R := Y.ringCatSheaf) I) :=
    Scheme.Modules.isFinitePresentation_sigma (fun _ : I ↦ SheafOfModules.unit Y.ringCatSheaf)
  have := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
    (SheafOfModules.free (R := Y.ringCatSheaf) I)
  have := Scheme.Modules.isQuasicoherent_tensorObj E ((M.tensorPow c).tensorPow m)
  have := Scheme.Modules.isFinitePresentation_tensorObj E ((M.tensorPow c).tensorPow m)
  have hKq : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) (kernel φ) :=
    Scheme.Modules.isQuasicoherent_kernel φ
  have hKf : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) (kernel φ) :=
    Scheme.Modules.isFinitePresentation_kernel φ
  have hCq := Scheme.Modules.isQuasicoherent_cokernel φ
  have hCf := Scheme.Modules.isFinitePresentation_cokernel φ
  obtain ⟨PK, hPK, hPK'⟩ := @Scheme.Modules.exists_polynomial_eulerChar_tensorObj_tensorPow _ K _
    _ _ _ hample g V hdim (kernel φ) hKq hKf hK
  obtain ⟨PC, hPC, hPC'⟩ := @Scheme.Modules.exists_polynomial_eulerChar_tensorObj_tensorPow _ K _
    _ _ _ hample g V hdim (cokernel φ) hCq hCf hC
  obtain ⟨PE, hPE, hPE'⟩ := Scheme.Modules.exists_polynomial_eulerChar_tensorObj_tensorPow_of_le K
    hample E (Scheme.Modules.topologicalKrullDim_le_unbotD_toNat K)
  obtain ⟨PO, hPO, hPO'⟩ := f.exists_polynomial_hilbertFunction M hample
  -- `χ(E ⊗ M^{⊗ (n + c m)}) = r χ(M^{⊗ n}) + χ(coker φ ⊗ M^{⊗ n}) - χ(ker φ ⊗ M^{⊗ n})`
  have key (n : ℕ) : (Scheme.Modules.eulerChar K (E ⊗ M.tensorPow (n + c * m)) : ℚ) =
      r * f.hilbertFunction M n + (Scheme.Modules.eulerChar K (cokernel φ ⊗ M.tensorPow n) -
        Scheme.Modules.eulerChar K (kernel φ ⊗ M.tensorPow n)) := by
    have h := Scheme.Modules.eulerChar_tensorObj_sub_eulerChar_tensorObj_eq K φ (M.tensorPow n)
    let e₂ : (M.tensorPow c).tensorPow m ⊗ M.tensorPow n ≅ M.tensorPow (n + c * m) :=
      whiskerRightIso (M.tensorPowMulIso c m).symm _ ≪≫ (M.tensorPowAddIso (c * m) n).symm ≪≫
        eqToIso (congrArg M.tensorPow (Nat.add_comm (c * m) n))
    let e₁ := α_ E ((M.tensorPow c).tensorPow m) (M.tensorPow n) ≪≫ whiskerLeftIso E e₂
    rw [Scheme.Modules.eulerChar_congr K e₁,
      Scheme.Modules.eulerChar_free_tensorObj K r (M.tensorPow n)] at h
    have h' : Scheme.Modules.eulerChar K (E ⊗ M.tensorPow (n + c * m)) =
        r * f.hilbertFunction M n + (Scheme.Modules.eulerChar K (cokernel φ ⊗ M.tensorPow n) -
          Scheme.Modules.eulerChar K (kernel φ ⊗ M.tensorPow n)) := by
      change _ = _ * Scheme.Modules.eulerChar K (M.tensorPow n) + _
      linarith
    exact_mod_cast h'
  have hpoly : PE.comp (Polynomial.X + Polynomial.C ((c * m : ℕ) : ℚ)) =
      (r : ℚ) • PO + (PC - PK) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _
      (Set.infinite_range_of_injective Nat.cast_injective |>.mono ?_)
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_smul, Polynomial.eval_sub, smul_eq_mul]
    have := hPE' (n + c * m)
    push_cast at this ⊢
    rw [this, key n, hPO' n, hPC' n, hPK' n]
  -- compare the coefficients of `X ^ g`
  have hcoeff : PE.coeff g = r * PO.coeff g := by
    rw [← Polynomial.coeff_comp_X_add_C_of_natDegree_le hPE ((c * m : ℕ) : ℚ), hpoly,
      Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_sub,
      Polynomial.coeff_eq_zero_of_degree_lt hPC, Polynomial.coeff_eq_zero_of_degree_lt hPK]
    simp [g]
  have hdeg := f.degree_eq_factorial_mul_coeff M hPO hPO'
  have hE : ((Δ_[1] ^[g] (fun m ↦ Scheme.Modules.eulerChar K (E ⊗ M.tensorPow m)) 0 : ℤ) : ℚ) =
      Δ_[1] ^[g] (fun n : ℕ ↦ PE.eval (n : ℚ)) 0 := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [hPE']
  rw [Polynomial.fwdDiff_iter_eval_natCast_zero hPE, hcoeff] at hE
  have : ((Δ_[1] ^[g] (fun m ↦ Scheme.Modules.eulerChar K (E ⊗ M.tensorPow m)) 0 : ℤ) : ℚ) =
      ((r * f.degree M : ℤ) : ℚ) := by
    rw [hE]
    push_cast
    rw [hdeg]
    ring
  exact_mod_cast this

/-- **Degree of a pullback under a finite morphism.** Let `g: X ⟶ Y` be a finite surjective
morphism of proper integral `K`-schemes, let `M` be an ample invertible `𝒪_Y`-module and let
`d = [k(X): k(Y)]` be the degree of `g`. Then `deg_{g^*M}(X) = d * deg_M(Y)`.

```
  X ────────── g ─────────▶ Y
    ╲                       │
     ╲  fX                  │ fY
      ╲                     ▼
       ╲───────────▶ Spec K
```
-/
theorem Scheme.Hom.degree_pullback [IsIntegral X] [IsIntegral Y] (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsFinite g] [Surjective g] (M : Y.Modules) (hample : IsAmple fY M) :
    fX.degree ((Scheme.Modules.pullback g).obj M) =
      g.finrank (genericPoint Y) * fY.degree M := by
  have := hample.isInvertible
  subst hg
  let : Y.Over (Spec (.of K)) := ⟨fY⟩
  let : X.Over (Spec (.of K)) := ⟨g ≫ fY⟩
  have : g.IsOver (Spec (.of K)) := ⟨rfl⟩
  have := LocallyOfFiniteType.isLocallyNoetherian fY
  have := Scheme.Modules.isFinitePresentation_pushforward_unit g
  obtain ⟨U, hU, ⟨e⟩⟩ := Scheme.Modules.exists_pullback_pushforward_unit_iso_free g
  rw [← fY.fwdDiff_iter_eulerChar_tensorObj_tensorPow M hample _ hU e, degree,
    g.topologicalKrullDim_eq_of_surjective]
  refine congrArg (fun F : ℕ → ℤ ↦ (fwdDiff 1)^[_] F 0) (funext fun m ↦ ?_)
  -- `χ(X, (g^* M)^{⊗ m}) = χ(X, g^* M^{⊗ m}) = χ(Y, g_* g^* M^{⊗ m}) = χ(Y, g_* 𝒪_X ⊗ M^{⊗ m})`
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso g M m
  obtain ⟨e₂⟩ := Scheme.Modules.nonempty_pushforward_pullback_iso g (M.tensorPow m)
  change Scheme.Modules.eulerChar K _ = _
  rw [← Scheme.Modules.eulerChar_congr K e₁, ← Scheme.Modules.eulerChar_congr K e₂,
    Scheme.Modules.eulerChar_pushforward_of_isAffineHom]

end AlgebraicGeometry
