/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Curve.Picard

/-!
# The Picard group of a proper curve splits as `ℤ × Pic⁰`

Source: blueprint, `sec-curve-estimates/det-def-pic`, node corollary-degree-jacobian--1,
order 888 (blueprint: corollary-degree-jacobian--1).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Source: blueprint, `sec-curve-estimates/det-def-pic`, node corollary-degree-jacobian--1,
order 888 (blueprint: corollary-degree-jacobian--1).

Let `C` be a proper smooth connected curve over the algebraically closed field `k`. The degree
sequence `0 → Pic⁰(C) → Pic(C) → ℤ → 0` splits: `Pic⁰(C)` is a subgroup `P0` of `Pic(C)` with
underlying set `f.picZero`, and there is an isomorphism `Pic(C) ≅ ℤ × Pic⁰(C)` (`ℤ` written
multiplicatively, as the group law of `Pic(C)`) whose first component is the degree and which
restricts to the identity on `Pic⁰(C)`.

Proof, step 1: by lem-sc-smooth-connected-curve-local-rings (2) `C` has a closed point `P`,
which is `k`-rational by lem-weil-pbc-closed-point-residue-field-base. The degree of
corollary-degree-jacobian--1 is the degree of divisors transported along `Cl(C) ≅ Pic(C)`
(proposition-cohomology-smooth-affine-curve, well defined by
theorem-riemann-roch-coherent-serre-duality), a homomorphism; `λ = [𝒪_C(P)]` has degree
`deg [P] = 1` (def-sc-divisor), so `s : n ↦ λ^n` is a homomorphism with `deg ∘ s = id`, and the
degree is surjective. Step 2: `Pic⁰(C) = ker deg`, so the sequence is exact at `Pic⁰(C)` and at
`Pic(C)`, and step 1 gives exactness at `ℤ`. The map `x ↦ (deg x, x · s(deg x)⁻¹)` lands in
`ℤ × Pic⁰(C)`, is a homomorphism, and has inverse `(n, y) ↦ s(n) · y`; its first component is the
degree and it restricts to the identity on `Pic⁰(C)`, i.e. the sequence splits. -/
theorem Scheme.Hom.exists_mulEquiv_prod_picZero
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] :
    ∃ (P0 : Subgroup C.Pic) (_ : (P0 : Set C.Pic) = f.picZero)
      (e : C.Pic ≃* Multiplicative ℤ × P0),
      (∀ L, (e L).1 = Multiplicative.ofAdd (f.picDegree L)) ∧
      ∀ y : P0, e y = (1, y) := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  let d := Scheme.picDegreeHom k C
  obtain ⟨g, hg⟩ := Scheme.surjective_picDegreeHom (k := k) (C := C)
    (Multiplicative.ofAdd 1)
  let σ : Multiplicative ℤ →* C.Pic := zpowersHom C.Pic g
  have hσ (n : Multiplicative ℤ) : d (σ n) = n := by
    rw [zpowersHom_apply, map_zpow, hg, ← ofAdd_zsmul,
      smul_eq_mul, mul_one, ofAdd_toAdd]
  let e : C.Pic ≃* Multiplicative ℤ × d.ker := {
    toFun L := (d L, ⟨L * (σ (d L))⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]⟩)
    invFun p := σ p.1 * p.2
    left_inv L := by simp
    right_inv p := by
      have h2 : d p.2 = 1 := p.2.2
      have h : d (σ p.1 * p.2) = p.1 := by rw [map_mul, hσ, h2, mul_one]
      ext
      · exact h
      · simp [h]
    map_mul' L L' := by
      ext
      · exact map_mul d L L'
      · simp only [Prod.snd_mul, Subgroup.coe_mul]
        rw [map_mul d, map_mul σ, mul_inv]
        ac_rfl }
  refine ⟨d.ker, Scheme.coe_ker_picDegreeHom, e, fun _ ↦ rfl, ?_⟩
  intro y
  have hy : d y = 1 := y.property
  change (d y, _) = (1, y)
  ext
  · exact hy
  · simp [hy]

end AlgebraicGeometry
