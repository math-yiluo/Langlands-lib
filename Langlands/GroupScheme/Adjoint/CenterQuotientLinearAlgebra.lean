import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Algebra.GroupWithZero.Idempotent

/-! # Linear algebra for the quotient by the centre

Elementary matrix facts used to show that the conjugacy class of a point of a commutative
normal subgroup of a connected group moves that point only by unipotent factors:
block polynomials separating one eigenvalue from the others, commuting idempotents,
and the nilpotence of `γ' - γ` for commuting matrices whose eigenvalue blocks are nested. -/

noncomputable section

open Polynomial

namespace Langlands.GroupScheme.CenterQuotient

section Ring

variable {A : Type*} [Ring A]

/-- For commuting idempotents `P` and `P'`, the element `P P' + (1 - P)` is idempotent. -/
theorem isIdempotentElem_mul_add_one_sub {P P' : A} (hP : IsIdempotentElem P)
    (hP' : IsIdempotentElem P') (hc : Commute P P') :
    IsIdempotentElem (P * P' + (1 - P)) := by
  have h1 : P * P' * (1 - P) = 0 := by
    rw [mul_sub, mul_one, mul_assoc, ← hc.eq, ← mul_assoc, hP.eq, sub_self]
  have h2 : (1 - P) * (P * P') = 0 := by
    rw [sub_mul, one_mul, ← mul_assoc, hP.eq, sub_self]
  have h3 : P * P' * (P * P') = P * P' := by
    rw [mul_assoc, ← mul_assoc P' P, ← hc.eq, mul_assoc, ← mul_assoc, hP.eq, hP'.eq]
  have h4 : (1 - P) * (1 - P) = 1 - P := hP.one_sub.eq
  rw [IsIdempotentElem, add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add]

/-- A product of commuting elements `a, b` with `a - 1` and `b - 1` nilpotent has
`a b - 1` nilpotent. -/
theorem isNilpotent_mul_sub_one {a b : A} (hc : Commute a b) (ha : IsNilpotent (a - 1))
    (hb : IsNilpotent (b - 1)) : IsNilpotent (a * b - 1) := by
  have hc' : Commute (a - 1) (b - 1) :=
    (hc.sub_right (Commute.one_right a)).sub_left (Commute.one_left _)
  have hab : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  rw [hab]
  refine Commute.isNilpotent_add ?_ (Commute.isNilpotent_add ?_ (hc'.isNilpotent_mul_right ha)
    ha) hb
  · exact (hc'.mul_left (Commute.refl _)).add_left hc'
  · exact (Commute.refl _).mul_left hc'.symm

/-- The inverse of a unit `u` with `u - 1` nilpotent again has this property. -/
theorem isNilpotent_inv_sub_one (u : Aˣ) (hu : IsNilpotent ((u : A) - 1)) :
    IsNilpotent (((u⁻¹ : Aˣ) : A) - 1) := by
  have h : ((u⁻¹ : Aˣ) : A) - 1 = -(((u : A) - 1) * ((u⁻¹ : Aˣ) : A)) := by
    rw [sub_mul, Units.mul_inv, one_mul, neg_sub]
  rw [h]
  refine IsNilpotent.neg ?_
  refine Commute.isNilpotent_mul_right ?_ hu
  exact (Commute.units_inv_right (Commute.refl (u : A))).sub_left (Commute.one_left _)

/-- If `γ` is a unit commuting with `γ'` and `γ' - γ` is nilpotent, then `γ' γ⁻¹ - 1` is
nilpotent. -/
theorem isNilpotent_mul_inv_sub_one (γ : Aˣ) (γ' : A) (hc : Commute (γ : A) γ')
    (hn : IsNilpotent (γ' - γ)) : IsNilpotent (γ' * ((γ⁻¹ : Aˣ) : A) - 1) := by
  have h : γ' * ((γ⁻¹ : Aˣ) : A) - 1 = (γ' - γ) * ((γ⁻¹ : Aˣ) : A) := by
    rw [sub_mul, Units.mul_inv]
  rw [h]
  refine Commute.isNilpotent_mul_right ?_ hn
  exact ((Commute.units_inv_left hc).symm).sub_left
    (Commute.units_inv_right (Commute.refl (γ : A)))

end Ring

section Algebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- An element commuting with `b` commutes with every polynomial in `b`. -/
theorem commute_aeval_right {a b : A} (h : Commute a b) (Q : R[X]) :
    Commute a (aeval b Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial k c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c a).mul_right (h.pow_right k)

/-- Polynomials in commuting elements commute. -/
theorem commute_aeval {a b : A} (h : Commute a b) (P Q : R[X]) :
    Commute (aeval a P) (aeval b Q) :=
  (commute_aeval_right (commute_aeval_right h Q).symm P).symm

/-- Evaluating a polynomial at a conjugate `u a u⁻¹` conjugates its value at `a`. -/
theorem aeval_units_conj (u : Aˣ) (a : A) (P : R[X]) :
    aeval ((u : A) * a * ((u⁻¹ : Aˣ) : A)) P = u * aeval a P * ((u⁻¹ : Aˣ) : A) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow]
    simp only [mul_assoc]
    rw [← mul_assoc (algebraMap R A c) (u : A), Algebra.commutes c (u : A), mul_assoc]

end Algebra

section Matrix

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- An idempotent matrix with determinant `1` is the identity. -/
theorem eq_one_of_isIdempotentElem_of_det_eq_one {E : Matrix n n K} (hE : IsIdempotentElem E)
    (hdet : E.det = 1) : E = 1 :=
  (IsIdempotentElem.iff_eq_one_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det E).2 (hdet ▸ isUnit_one))).1 hE

/-- The determinant of an idempotent matrix is idempotent. -/
theorem isIdempotentElem_det {E : Matrix n n K} (hE : IsIdempotentElem E) :
    IsIdempotentElem E.det := by
  rw [IsIdempotentElem, ← Matrix.det_mul, hE.eq]

/-- A nilpotent matrix over a field satisfies `N ^ card n = 0`. -/
theorem pow_card_eq_zero_of_isNilpotent {N : Matrix n n K} (hN : IsNilpotent N) :
    N ^ Fintype.card n = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  rw [isNilpotent_iff_eq_zero, sub_eq_zero] at h
  have := Matrix.aeval_self_charpoly N
  rwa [h, map_pow, aeval_X] at this

/-- Every eigenvalue of a matrix `A` with `A - 1` nilpotent is `1`. -/
theorem eq_one_of_mem_roots_of_isNilpotent_sub_one {A : Matrix n n K}
    (hA : IsNilpotent (A - 1)) {c : K} (hc : c ∈ A.charpoly.roots) : c = 1 := by
  have hroot : A.charpoly.IsRoot c := (mem_roots A.charpoly_monic.ne_zero).1 hc
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) c := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hv' : Matrix.toLin' (A - 1) v = (c - 1) • v := by
    rw [map_sub, LinearMap.sub_apply, hv.apply_eq_smul, Matrix.toLin'_one, sub_smul,
      LinearMap.id_apply, one_smul]
  have hev' : Module.End.HasEigenvalue (Matrix.toLin' (A - 1)) (c - 1) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hv', hv.2⟩
  have hnil : IsNilpotent (Matrix.toLin' (A - 1)) :=
    hA.map (Matrix.toLinAlgEquiv' (R := K) (n := n))
  have := hev'.isNilpotent_of_isNilpotent hnil
  rw [isNilpotent_iff_eq_zero, sub_eq_zero] at this
  exact this

/-- For a root `c` of the characteristic polynomial of `γ`, a polynomial `P` with
`P(c) = 1`, vanishing at every other root, such that `P(γ)` is idempotent: the projector
onto the generalized `c`-eigenspace of `γ` along the other generalized eigenspaces. -/
theorem exists_blockPolynomial (γ : Matrix n n K) {c : K} (hc : γ.charpoly.IsRoot c) :
    ∃ P : K[X], P.eval c = 1 ∧ (∀ μ, γ.charpoly.IsRoot μ → μ ≠ c → P.eval μ = 0) ∧
      IsIdempotentElem (aeval γ P) := by
  set q := γ.charpoly with hqdef
  have hq0 : q ≠ 0 := γ.charpoly_monic.ne_zero
  obtain ⟨r, hq, hr⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 c
  set m := q.rootMultiplicity c with hmdef
  have hm : 0 < m := (rootMultiplicity_pos hq0).2 hc
  obtain ⟨u, w, huw⟩ :=
    ((irreducible_X_sub_C c).coprime_pow_of_not_dvd m hr).symm
  refine ⟨w * r, ?_, ?_, ?_⟩
  · have := congrArg (eval c) huw
    simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow hm.ne', mul_zero, zero_add, eval_one] at this
    simpa using this
  · intro μ hμ hμc
    have hqμ : q.eval μ = 0 := hμ
    rw [hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hqμ
    have hrμ : r.eval μ = 0 := by
      rcases mul_eq_zero.1 hqμ with h | h
      · exact absurd (sub_eq_zero.1 (pow_eq_zero_iff hm.ne' |>.1 h)) hμc
      · exact h
    simp [hrμ]
  · have h1 : aeval γ (u * (X - C c) ^ m) = 1 - aeval γ (w * r) := by
      rw [eq_sub_iff_add_eq, ← map_add, huw, map_one]
    have h2 : aeval γ (w * r) * aeval γ (u * (X - C c) ^ m) = 0 := by
      rw [← map_mul]
      have : w * r * (u * (X - C c) ^ m) = w * u * q := by
        rw [hq]
        ring
      rw [this, map_mul, Matrix.aeval_self_charpoly, mul_zero]
    rw [h1, mul_sub, mul_one, sub_eq_zero] at h2
    exact h2.symm

variable [IsAlgClosed K]

/-- A matrix over an algebraically closed field that is not nilpotent has a nonzero
eigenvalue. -/
theorem exists_isRoot_ne_zero_of_not_isNilpotent {N : Matrix n n K} (hN : ¬IsNilpotent N) :
    ∃ d : K, N.charpoly.IsRoot d ∧ d ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hN
  have hsplit := (IsAlgClosed.splits N.charpoly).eq_prod_roots_of_monic N.charpoly_monic
  have hroots : N.charpoly.roots = Multiset.replicate (Multiset.card N.charpoly.roots) 0 :=
    Multiset.eq_replicate_of_mem fun b hb =>
      hcon b ((mem_roots N.charpoly_monic.ne_zero).1 hb)
  refine ⟨Multiset.card N.charpoly.roots, ?_⟩
  have h := Matrix.aeval_self_charpoly N
  rw [hsplit, hroots, Multiset.map_replicate, Multiset.prod_replicate, map_pow, map_sub,
    aeval_X, aeval_C, map_zero, sub_zero] at h
  exact h

/-- **Nested blocks force a nilpotent difference.** Let `γ` and `γ'` be commuting matrices
over an algebraically closed field. Suppose that for every eigenvalue `c` of `γ` and every
different eigenvalue `c'` of `γ'` there is a polynomial `P` with `P(c) = 1`, `P(c') = 0` and
`P(γ) P(γ') = P(γ)`. Then `γ' - γ` is nilpotent.

Otherwise `γ' - γ` has an eigenvalue `d ≠ 0`; as `γ` preserves the `d`-eigenspace it has an
eigenvector `w` there, with eigenvalue `c`, and `γ' w = (c + d) w`. Then `P(γ) w = w` while
`P(γ) P(γ') w = 0`. -/
theorem isNilpotent_sub_of_forall_blockPolynomial (γ γ' : Matrix n n K) (hcomm : Commute γ γ')
    (hblock : ∀ c c' : K, c ≠ c' → γ.charpoly.IsRoot c → γ'.charpoly.IsRoot c' →
      ∃ P : K[X], P.eval c = 1 ∧ P.eval c' = 0 ∧ aeval γ P * aeval γ' P = aeval γ P) :
    IsNilpotent (γ' - γ) := by
  by_contra hN
  obtain ⟨d, hd, hd0⟩ := exists_isRoot_ne_zero_of_not_isNilpotent hN
  let e := Matrix.toLinAlgEquiv' (R := K) (n := n)
  set f : Module.End K (n → K) := e γ with hfdef
  set f' : Module.End K (n → K) := e γ' with hf'def
  set N : Module.End K (n → K) := e (γ' - γ) with hNdef
  have hNf : N = f' - f := by rw [hNdef, map_sub]
  have hfN : Commute f N := by
    rw [hNf]
    exact ((hcomm.map e).sub_right (Commute.refl _))
  have hNd : N.HasEigenvalue d := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    change (Matrix.toLin' (γ' - γ)).charpoly.IsRoot d
    rw [Matrix.charpoly_toLin']
    exact hd
  have hmaps := Module.End.mapsTo_genEigenspace_of_comm hfN.symm d 1
  have : Nontrivial (N.eigenspace d) := Submodule.nontrivial_iff_ne_bot.2 hNd
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict (p := N.eigenspace d) (q := N.eigenspace d) fun x hx => hmaps hx)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  set v : n → K := (w : n → K) with hvdef
  have hv0 : v ≠ 0 := by
    intro h
    exact hw.2 (Subtype.ext h)
  have hfv : f v = c • v := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa [LinearMap.restrict_apply] using this
  have hNv : N v = d • v := Module.End.mem_eigenspace_iff.1 w.2
  have hf'v : f' v = (c + d) • v := by
    have : f' = f + N := by rw [hNf]; abel
    rw [this, LinearMap.add_apply, hfv, hNv, add_smul]
  have hfc : f.HasEigenvector c v := ⟨Module.End.mem_eigenspace_iff.2 hfv, hv0⟩
  have hf'c : f'.HasEigenvector (c + d) v := ⟨Module.End.mem_eigenspace_iff.2 hf'v, hv0⟩
  have hroot : γ.charpoly.IsRoot c := by
    have := (Module.End.hasEigenvalue_iff_isRoot_charpoly f c).1
      (Module.End.hasEigenvalue_of_hasEigenvector hfc)
    change (Matrix.toLin' γ).charpoly.IsRoot c at this
    rwa [Matrix.charpoly_toLin'] at this
  have hroot' : γ'.charpoly.IsRoot (c + d) := by
    have := (Module.End.hasEigenvalue_iff_isRoot_charpoly f' (c + d)).1
      (Module.End.hasEigenvalue_of_hasEigenvector hf'c)
    change (Matrix.toLin' γ').charpoly.IsRoot (c + d) at this
    rwa [Matrix.charpoly_toLin'] at this
  have hne : c ≠ c + d := by
    intro h
    exact hd0 (by linear_combination -h)
  obtain ⟨P, hPc, hPc', hP⟩ := hblock c (c + d) hne hroot hroot'
  have hPv : aeval f P v = v := by
    rw [Module.End.aeval_apply_of_hasEigenvector hfc, hPc, one_smul]
  have hP'v : aeval f' P v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hf'c, hPc', zero_smul]
  have hPe := congrArg e hP
  rw [map_mul, ← aeval_algHom_apply, ← aeval_algHom_apply] at hPe
  have := congrArg (fun φ : Module.End K (n → K) => φ v) hPe
  simp only [Module.End.mul_apply] at this
  change aeval f P (aeval f' P v) = aeval f P v at this
  rw [hP'v, map_zero, hPv] at this
  exact hv0 this.symm

end Matrix

end Langlands.GroupScheme.CenterQuotient
