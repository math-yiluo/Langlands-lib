/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Differential basis for a separably generated field extension

Source: Stacks Project, Algebra, proof of Tag 031W, expanded using Tags 00RX,
00RT, and 090W (blueprint: new-separably-generated-differentials-basis).
-/

@[expose] public section
universe u v
namespace KaehlerDifferential
/-- The basis-existence part of the separably generated differential theorem.

Source: Stacks Project, Algebra, the computation in the proof of Tag 031W,
expanded using Tags 00RX, 00RT, and 090W.

Proof: Set P = k[X_i], A = k[x_i], and F = k(x_i). Algebraic independence
identifies P with A through evaluation. Mathlib's intermediate-field fraction-ring
instance identifies F as the fraction field of A, and this transfers to P.
Thus P → F is formally étale, as a localization. The hypothesis hxs makes F → K
separable algebraic, hence formally étale by Tag 090W, without any finiteness
assumption. Composition makes P → K formally étale. The canonical differential
base-change isomorphism K ⊗[P] Ω[P/k] ≃ Ω[K/k] therefore carries the scalar extension
of the polynomial basis dX_i (Tag 00RX) to a K-basis. Its i-th vector is D(x_i),
by the formula for the differential base-change map and evaluation of X_i.
This also applies when r = 0. Both hfg and hsep are redundant in this argument;
they are retained unchanged to match the original statement.
(blueprint: new-separably-generated-differentials-basis) -/
theorem exists_basis_differentials_of_separating_transcendenceBasis_basis
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsep : Algebra.IsSeparableExtension k K)
    {r : ℕ} (x : Fin r → K) (hx : IsTranscendenceBasis k x)
    (hxs : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K) :
    ∃ b : Module.Basis (Fin r) K (KaehlerDifferential k K),
      ∀ i : Fin r, b i = D k K (x i) := by
  have _ := hfg
  have _ := hsep
  let P := MvPolynomial (Fin r) k
  let A := Algebra.adjoin k (Set.range x)
  let F := IntermediateField.adjoin k (Set.range x)
  let e : P ≃ₐ[k] A := hx.1.aevalEquiv
  let : Algebra P K := (MvPolynomial.aeval x).toRingHom.toAlgebra
  let : Algebra P F :=
    ((Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k
      (Set.range x))).comp e.toAlgHom).toRingHom.toAlgebra
  have : IsScalarTower k P K := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower k P F := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    change algebraMap k K a = (e (algebraMap k P a) : K)
    rw [e.commutes]
    rfl
  have : IsScalarTower P F K := IsScalarTower.of_algebraMap_eq fun p => by
    change MvPolynomial.aeval x p = (e p : K)
    exact (hx.1.algebraMap_aevalEquiv p).symm
  let : Algebra A F :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k
      (Set.range x))).toAlgebra
  have : FaithfulSMul A F :=
    Subalgebra.inclusion.faithfulSMul (IntermediateField.algebra_adjoin_le_adjoin k
      (Set.range x))
  have : IsFractionRing A F :=
    IsFractionRing.of_field _ _ fun ⟨_, h⟩ => by
      obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp h
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext hab⟩
  have : IsFractionRing P F := IsFractionRing.of_ringEquiv_left e.toRingEquiv
    (fun p => rfl)
  have : Algebra.FormallyEtale P F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  have : Algebra.IsSeparable F K := hxs
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  have : Algebra.FormallyEtale P K := Algebra.FormallyEtale.comp P F K
  refine ⟨((mvPolynomialBasis k (Fin r)).baseChange K).map
    (tensorKaehlerEquivOfFormallyEtale k P K), ?_⟩
  intro i
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
  change (tensorKaehlerEquivOfFormallyEtale k P K)
    (1 ⊗ₜ[P] (mvPolynomialBasis k (Fin r)) i) = D k K (x i)
  rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul,
    one_smul, mvPolynomialBasis_apply, map_D]
  congr 1
  exact MvPolynomial.aeval_X x i
end KaehlerDifferential
