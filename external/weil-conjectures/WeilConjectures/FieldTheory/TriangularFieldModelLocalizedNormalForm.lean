/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.TriangularFieldModelEquations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra

import WeilConjectures.FieldTheory.TriangularFieldModelReconstructionBijective

/-! # Unique localized coefficients for a triangular monic quotient -/

@[expose] public section

universe u v

namespace FieldTheory

/-- Successive monic division gives unique coefficients in the explicit localization.
Source: Stacks Project, Algebra, proof of Tag 07BV (the triangular monic quotient
before embedding it in the generated field), and Tag 08JZ (localization presentation).
(blueprint: lem-weil-pbc-triangular-field-model-localized-normal-form).

Proof: Set R = k[X] and D = R[1/h]. Identify the quotient by hT-1 with D
using the localization presentation. At stage i, regard the polynomial ring on
its first d+1+i variables modulo the preceding equations as the coefficient ring;
adjoining the next variable and quotienting by p_i is AdjoinRoot of the mapped
polynomial. Mapping preserves monicity. If e_i is positive, the leading
coefficient stays one and its degree stays e_i. The power basis of this monic
quotient has exponents below e_i. Inductively multiply these bases with the
previous D-basis and reindex the product by dependent exponent tuples. The
base case m=0 is D with its one-element basis. Splitting off the last variable
and the quotient universal property identify this iterated quotient with the
simultaneous ideal-of-list quotient. Restrict the D-linear coordinate equivalence
to k and identify finitely supported functions with functions on the finite
exponent set. This gives nf. Evaluation at y factors through the simultaneous
quotient by hzero. Its restriction to D is phi: the maps agree on R by hphi,
and the localization universal property determines the inverse of h. The
identifications hyx, hyt and hyb therefore evaluate each power-basis monomial
to the corresponding product of powers of b_i. Applying this evaluation map
to the finite basis expansion proves the formula. If some e_i=0, monicity
makes p_i=1; hzero would give 1=0 in K, so eliminate this impossible case.
No algebraic independence is needed. In particular this is a basis over D,
not a finite basis over k. -/
theorem triangularFieldModel_localized_normal_form
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (m : ℕ) (b : Fin m → K)
    (h : MvPolynomial (Fin d) k)
    (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (y : Fin (d + 1 + m) → K) (e : Fin m → ℕ)
    (hp : ∀ i, (p i).Monic) (he : ∀ i, (p i).natDegree = e i)
    (hyx : ∀ j : Fin d, y ⟨j.val, by omega⟩ = x j)
    (hyt : y ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹)
    (hyb : ∀ i : Fin m, y ⟨d + 1 + i.val, by omega⟩ = b i)
    (hzero : ∀ q ∈ triangularFieldModelEquations k d m h p,
      MvPolynomial.aeval y q = 0)
    (phi : Localization.Away h →ₐ[k] K)
    (hphi : ∀ r : MvPolynomial (Fin d) k,
      phi (algebraMap _ (Localization.Away h) r) = MvPolynomial.aeval x r) :
    ∃ nf : (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p)) ≃ₗ[k]
        (((i : Fin m) → Fin (e i)) → Localization.Away h),
      ∀ q : MvPolynomial (Fin (d + 1 + m)) k,
        MvPolynomial.aeval y q =
          ∑ a : ((i : Fin m) → Fin (e i)),
            phi (nf (Ideal.Quotient.mk _ q) a) * (∏ i, b i ^ (a i).val) := by
  classical
  have _hyt := hyt
  let I := Ideal.ofList (triangularFieldModelEquations k d m h p)
  let Q := MvPolynomial (Fin (d + 1 + m)) k ⧸ I
  let f : MvPolynomial (Fin d) k →ₐ[k] Q :=
    (Ideal.Quotient.mkₐ k I).comp (MvPolynomial.rename
      (fun j : Fin d ↦ (⟨j.val, by omega⟩ : Fin (d + 1 + m))))
  have hu : IsUnit (f h) := by
    rw [isUnit_iff_exists_inv]
    refine ⟨Ideal.Quotient.mk I (MvPolynomial.X ⟨d, by omega⟩), ?_⟩
    change Ideal.Quotient.mk I
      (MvPolynomial.rename (fun j : Fin d ↦
        (⟨j.val, by omega⟩ : Fin (d + 1 + m))) h) * _ = 1
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I),
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply Ideal.subset_span
    simp [triangularFieldModelEquations]
  let psi : Localization.Away h →ₐ[k] Q := IsLocalization.Away.liftAlgHom h hu
  have hpsi : ∀ r : MvPolynomial (Fin d) k,
      psi (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk I
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + m))) r) := by
    intro r
    simp only [psi, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  let L : (((i : Fin m) → Fin (e i)) → Localization.Away h) →ₗ[k] Q :=
    ∑ a : ((i : Fin m) → Fin (e i)),
      (LinearMap.mulRight k (∏ i : Fin m,
        (Ideal.Quotient.mk I (MvPolynomial.X
          (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val)).comp
            (psi.toLinearMap.comp (LinearMap.proj a))
  have hL : Function.Bijective L :=
    triangularFieldModel_reconstruction_bijective k d m h p e hp he psi hpsi
  let nf := (LinearEquiv.ofBijective L hL).symm
  have hI : I ≤ RingHom.ker (MvPolynomial.aeval y).toRingHom := by
    apply Ideal.span_le.mpr
    intro q hq
    exact RingHom.mem_ker.mpr (hzero q hq)
  let ev : Q →ₐ[k] K := Ideal.Quotient.liftₐ I (MvPolynomial.aeval y)
    (fun q hq ↦ RingHom.mem_ker.mp (hI hq))
  have hev : ∀ q, ev (Ideal.Quotient.mk I q) = MvPolynomial.aeval y q := by
    intro q
    rfl
  have hcomp : ev.comp psi = phi := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    apply RingHom.ext
    intro r
    change ev (psi (algebraMap _ (Localization.Away h) r)) =
      phi (algebraMap _ (Localization.Away h) r)
    rw [hpsi, hev, hphi]
    rw [MvPolynomial.aeval_rename]
    have H : y ∘ (fun j : Fin d ↦
        (⟨j.val, by omega⟩ : Fin (d + 1 + m))) = x := funext hyx
    rw [H]
  refine ⟨nf, ?_⟩
  intro q
  have hrec : L (nf (Ideal.Quotient.mk I q)) = Ideal.Quotient.mk I q :=
    (LinearEquiv.ofBijective L hL).apply_symm_apply _
  rw [← hev q]
  conv_lhs => rw [← hrec]
  dsimp only [L]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
    map_sum, map_mul, map_prod, map_pow]
  apply Finset.sum_congr rfl
  intro a ha
  change ev (psi (nf (Ideal.Quotient.mk I q) a)) *
    (∏ i : Fin m, ev (Ideal.Quotient.mk I (MvPolynomial.X
      (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val) = _
  rw [← AlgHom.comp_apply, hcomp]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hev, MvPolynomial.aeval_X, hyb]

end FieldTheory
