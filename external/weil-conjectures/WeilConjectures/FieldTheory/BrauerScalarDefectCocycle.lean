/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectScalarData
import WeilConjectures.FieldTheory.BrauerScalarDefectCocycleRealization

/-!
# The continuous scalar-defect cocycle

Source: Stacks Project, Lemma 03R6, construction before Theorem 03R7, and Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-cocycle).
-/

@[expose] public section
universe u
namespace Field

open scoped TensorProduct
/-- The scalar defect of locally constant lifts is represented by a homogeneous cocycle.
Proof: write X_a = e(1 ⊗ a). Applying g to the identity for h and then the identity
for g shows that b_g g(b_h) and b_(gh) induce the same conjugation on every X_a.
The X_a span the matrix algebra over the separable closure, since every tensor is a
sum of scalar multiples of 1 ⊗ a and e is surjective. Thus their quotient
D(g,h) = b_g g(b_h) b_(gh)⁻¹ commutes with every matrix. A matrix commuting with all
matrix units is scalar: commutation with the diagonal units kills its off-diagonal
entries, and commutation with the other units makes its diagonal entries equal.
Since n is positive and D is invertible, that scalar is a unique unit c(g,h).
Expand b_g g(b_h) gh(b_k) in the two associative orders and cancel b_(ghk).
This gives c(g,h)c(gh,k) = g(c(h,k))c(g,hk).
The function c is jointly locally constant. Near any (g,h), b_g, b_h and b_(gh) are
constant by local constancy of b and continuity of group multiplication; the action
of g on the finitely many entries of the fixed b_h is locally constant by openness
of their Galois stabilizers. Extracting a diagonal entry of D preserves local
constancy. The action on any fixed unit is similarly locally constant.
Set f(g₀,g₁,g₂) = g₀(c(g₀⁻¹g₁,g₁⁻¹g₂)), and use Additive.ofMul on its values.
This is jointly continuous into the discrete coefficient module and equivariant for
simultaneous left translation. The displayed multiplicative cocycle identity says
that its alternating homogeneous differential vanishes. The absolute Galois group
is compact Hausdorff; the compact-open exponential law curries this jointly
continuous map into Mathlib's iterated continuous cochains. Equivariance puts it
in the invariant cochains, and vanishing differential gives an element z of the
cycles object. Evaluation at (1,g,gh) recovers c(g,h). Its defining scalar matrix
identity is exactly the conclusion. Neither normalization of b nor of c is needed.

Source: Stacks Project, scalar-defect construction preceding Theorem 03R7 and Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-cocycle). -/
theorem exists_brauerScalarDefect_cocycle (K : Type u) [Field K] (A : CSA.{u, u} K)
    (n : ℕ) (hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) :
    ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
      ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
          b (g * h) := by
  obtain ⟨c, hlc, hrel, hc⟩ := exists_brauerScalarDefect_scalar_data K A n hn e b hb hdesc
  obtain ⟨z, hz⟩ := exists_galoisUnits_cocycle_of_scalar_cocycle K c hlc hc
  refine ⟨z, ?_⟩
  intro g h
  simpa [hz g h] using hrel g h
end Field
