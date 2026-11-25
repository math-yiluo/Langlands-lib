/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor

/-!
# Affine fibre rings over a discrete valuation ring

Source: Stacks Project, Tag 055J, proof, affine fibre identifications.
-/

@[expose] public section

universe u
open CategoryTheory IsLocalRing
namespace AlgebraicGeometry

/-- The generic fibre over an affine open has its localization ring, compatibly with
restriction, and the reduced closed fibre makes the uniformizer quotient reduced.

Source: Stacks Project, Tag 055J, proof, the identifications of the affine fibre rings.
Proof: Put A = Γ(X,U) and let ρ : R → A be induced by f. The affine fibre-product
formula identifies the preimage of U in each scheme-theoretic fibre with
Spec(κ(p) ⊗[R] A), compatibly with the map a ↦ 1 ⊗ a. For the zero prime of a DVR,
κ(0) is its fraction field. Every nonzero r ∈ R is a unit times a power of the
uniformizer π, so this field is R[1/π]. Base change of localization identifies
κ(0) ⊗[R] A with A[1/ρ(π)], compatibly with A. Composing these canonical
identifications with the spectrum global-sections isomorphism gives ε and its
displayed equation. For the closed point, κ(m) = R/m = R/(π). Tensoring this
quotient with A gives A/ρ(π)A. The corresponding affine fibre is an open subscheme
of the assumed reduced closed fibre, hence its ring of sections, and therefore
A/ρ(π)A, is reduced. No flatness, connectedness, nonemptiness or finiteness is
needed for these ring identifications. If U is empty, all three rings are zero.
(blueprint: lem-sbc-generic-fibre-affine-ring-models) -/
theorem generic_fibre_affine_ring_models {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsReduced (f.fiber (closedPoint R))] (U : X.affineOpens)
    (π : R) (hπ : Irreducible π) :
    let ρ := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top
    _root_.IsReduced (Γ(X, U.1) ⧸ Ideal.span {ρ π}) ∧
      ∃ ε : Γ(f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R),
          (f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) ⁻¹ᵁ U.1) ≃+*
          Localization.Away (ρ π),
        ∀ a : Γ(X, U.1),
          ε ((f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).app U.1 a) =
            algebraMap Γ(X, U.1) (Localization.Away (ρ π)) a := by
  classical
  dsimp only
  let A := Γ(X, U.1)
  let ρ := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top
  let : Algebra R A := ρ.hom.toAlgebra
  obtain ⟨ec, _⟩ := affine_fibre_sections_tensor f U (closedPoint R)
  have : _root_.IsReduced (TensorProduct R A (maximalIdeal R).ResidueField) :=
    isReduced_of_injective ec.symm.toRingHom ec.symm.injective
  let q : (R ⧸ maximalIdeal R) ≃ₐ[R] (maximalIdeal R).ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ maximalIdeal R) _)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  let eqc :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal R)).toRingEquiv.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[R] A) q).toRingEquiv
  have hmap : (maximalIdeal R).map (algebraMap R A) = Ideal.span {ρ π} := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ
    rw [hπ, Ideal.map_span, Set.image_singleton]
    rfl
  constructor
  · rw [← hmap]
    exact isReduced_of_injective eqc.toRingHom eqc.injective
  · let K := (⊥ : Ideal R).ResidueField
    have hle : Submonoid.powers π ≤ nonZeroDivisors R := by
      rintro x ⟨n, rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hπ.ne_zero)
    have hdvd : ∀ x ∈ nonZeroDivisors R, ∃ y ∈ Submonoid.powers π, x ∣ y := by
      intro x hx
      obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
        (mem_nonZeroDivisors_iff_ne_zero.mp hx) hπ
      exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
    have : IsLocalization.Away π K :=
      (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers π)
        (nonZeroDivisors R) hle hdvd).mpr inferInstance
    obtain ⟨eg, hg⟩ := affine_fibre_sections_tensor f U
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let el := IsLocalization.Away.tensorEquiv (R := R) (r := π) (A := K) A
    refine ⟨eg.trans el.toRingEquiv, ?_⟩
    intro a
    rw [RingEquiv.trans_apply, hg]
    exact el.commutes a

end AlgebraicGeometry
