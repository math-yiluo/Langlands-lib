/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectTensorLifts
import WeilConjectures.FieldTheory.GaloisUnitsScalarCoboundary
import WeilConjectures.FieldTheory.GaloisMatrixCocycleSplit

/-!
# Splitting the tensor product of scalar-defect realizations

Source: Stacks Project, Tag 03R7, injectivity argument, and Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-tensor-split).
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- Equal scalar-defect classes split the tensor product with the opposite algebra.

Proof: choose the matrix splittings and locally constant lifts supplied by the two
scalar-defect realizations. Transpose the second splitting to identify its opposite
with a matrix algebra, and use the inverse transpose of its lifts. The Kronecker
product with the first lifts realizes the tensor descent datum, with scalar defect
`c_z / c_w`. Equality of the two homogeneous cohomology classes says that `z - w`
is a continuous coboundary. Evaluate a homogeneous one-cochain witnessing this
boundary at `(1,g)` to obtain a locally constant scalar cochain `a(g)` with
`c_z(g,h) / c_w(g,h) = a(g) * g(a(h)) / a(g*h)`.
Rescale the tensor lifts by `a(g)⁻¹`; the new lifts are a genuine general-linear
one-cocycle. Compactness of the absolute Galois group and local constancy allow
all lifts, the scalar cochain, and the finitely many splitting coefficients to be
handled over a common finite Galois extension. Matrix Hilbert 90, equivalently
finite Galois descent of vector spaces, trivializes this cocycle. Conjugating the
tensor splitting by the trivializing matrix makes its descent datum coefficientwise
Galois action. Taking fixed points gives a K-algebra isomorphism from `A ⊗ Bᵐᵒᵖ`
to a matrix algebra over K. Its size is the product of the two positive splitting
sizes, hence is nonzero. No Brauer equivalence criterion is used in this step.
Source: Stacks Project, Tag 03R7, injectivity argument; Section 0DVG for the
homogeneous-to-inhomogeneous coboundary convention.
(blueprint: lem-sc-brauer-scalar-defect-tensor-split). -/
theorem tensor_opposite_split_of_brauerScalarDefect_eq (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : x = y) :
    ∃ n : ℕ, n ≠ 0 ∧ Nonempty ((A ⊗[K] Bᵐᵒᵖ) ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, hn, e, b, z, w, hb, hz, hw, hdesc, hdef⟩ :=
    exists_tensor_opposite_scalarDefect_lifts K A B x y hx hy
  obtain ⟨a, ha, hratio⟩ :=
    exists_scalar_cochain_of_galoisUnits_class_eq K z w (hz.trans (h.trans hw.symm))
  let s := Matrix.GeneralLinearGroup.scalar (Fin n) (R := SeparableClosure K)
  let b' : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K) := fun g ↦ s (a g)⁻¹ * b g
  have hb' : IsLocallyConstant b' := (ha.inv.comp s).mul hb
  have hcoc : ∀ g h, b' g * Matrix.GeneralLinearGroup.map g.toRingHom (b' h) =
      b' (g * h) := by
    intro g h
    dsimp only [b']
    rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_scalar]
    change s (a g)⁻¹ * b g * (s (Units.map g.toRingHom (a h)⁻¹) *
      Matrix.GeneralLinearGroup.map g.toRingHom (b h)) = s (a (g * h))⁻¹ * b (g * h)
    rw [← mul_assoc, mul_assoc (s (a g)⁻¹) (b g),
      ← Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc,
      mul_assoc (s (a g)⁻¹ * _), hdef, hratio]
    rw [← mul_assoc, ← map_mul s, ← map_mul s]
    have hu : (a g)⁻¹ * Units.map g.toRingHom (a h)⁻¹ *
        (a g * Units.map g.toRingHom (a h) / a (g * h)) = (a (g * h))⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    rw [hu]
  have hdesc' : ∀ (g : Gal(SeparableClosure K/K)) (d : A ⊗[K] Bᵐᵒᵖ),
      (e (1 ⊗ₜ[K] d)).map g =
        ((b' g)⁻¹).val * e (1 ⊗ₜ[K] d) * (b' g).val := by
    intro g d
    rw [hdesc]
    dsimp only [b']
    rw [mul_inv_rev, Units.val_mul, Units.val_mul]
    have hs : (s (a g)⁻¹)⁻¹ = s (a g) := by simp only [map_inv, inv_inv]
    rw [hs]
    have hcomm : (s (a g)).val * e (1 ⊗ₜ[K] d) =
        e (1 ⊗ₜ[K] d) * (s (a g)).val :=
      by
        change Matrix.scalar (Fin n) (a g : SeparableClosure K) * e (1 ⊗ₜ[K] d) =
          e (1 ⊗ₜ[K] d) * Matrix.scalar (Fin n) (a g : SeparableClosure K)
        exact Matrix.scalar_comm _ (Commute.all _) _
    symm
    rw [mul_assoc ((b g)⁻¹).val (s (a g)).val (e (1 ⊗ₜ[K] d)), hcomm]
    simp only [mul_assoc]
    rw [← mul_assoc (s (a g)).val, ← Units.val_mul, ← map_mul]
    simp
  exact ⟨n, hn, nonempty_algEquiv_matrix_of_galois_cocycle K
    (A ⊗[K] Bᵐᵒᵖ) n e b' hb' hdesc' hcoc⟩

end Field
