/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Spec
import WeilConjectures.AlgebraicGeometry.SpreadFiniteSeparableExtension
import WeilConjectures.AlgebraicGeometry.SpreadPurelyInseparableFactors
import WeilConjectures.FieldTheory.GenericSeparableAlgebraSplitting
import WeilConjectures.AlgebraicGeometry.SpreadGenericProductDomains
import WeilConjectures.AlgebraicGeometry.RefineFiniteDomainSplitting

/-!
# Generic splitting of a finite algebra after an étale base change

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9
(blueprint: lem-weil-pbc-generic-finite-algebra-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open AlgebraicGeometry

/--
A finite algebra `B` over a Noetherian domain `A` splits generically: after inverting a nonzero
`c` and a finite étale surjective base change `A[1/c] → A'`, the reduction of `B ⊗[A] A'` is a
finite product of finite `A'`-domains `D j`, each `Spec (D j) → Spec A'` finite, surjective and a
universal homeomorphism (every base change a homeomorphism). The fraction field `K` of the node
is only named there; it is not a datum of the statement.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof steps 4--9
(blueprint: lem-weil-pbc-generic-finite-algebra-splitting).

Proof: pass to the generic fibre `C = B ⊗[A] K`, a finite-dimensional `K`-algebra, and apply
`lem-weil-pbc-generic-separable-algebra-splitting`: after a finite separable `K'/K` the
reduction of `C ⊗[K] K'` is a product of finite purely inseparable fields `L j`. Spread `K'/K`
to a finite étale surjective `A[1/c] → A'` by `lem-weil-pbc-spread-finite-separable-extension`.
After a further principal localization, `(B ⊗[A] A')_red` is torsion free with generic fibre
`(C ⊗[K] K')_red = ∏ L j` (reduction commutes with localization); clearing denominators in the
generic idempotents splits it as a product of finite domains `D j` with fraction fields `L j`.
Each `A' → D j` is then finite, surjective and a universal homeomorphism by
`lem-weil-pbc-spread-purely-inseparable-factors`.
-/
theorem exists_generic_finite_algebra_splitting
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B] :
    ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
      (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A'),
      c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
        Algebra.Etale (Localization.Away c) A' ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))) ∧
        ∃ (r : ℕ) (D : Fin r → Type u) (_ : ∀ j, CommRing (D j))
          (_ : ∀ j, Algebra A' (D j)),
          (∀ j, Module.Finite A' (D j) ∧ IsDomain (D j) ∧
            IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A' (D j)))) ∧
            Surjective (Spec.map (CommRingCat.ofHom (algebraMap A' (D j)))) ∧
            (topologically IsHomeomorph).universally
              (Spec.map (CommRingCat.ofHom (algebraMap A' (D j))))) ∧
          letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A')
          Nonempty (((B ⊗[A] A') ⧸ nilradical (B ⊗[A] A')) ≃ₐ[A'] (∀ j, D j)) := by
  classical
  let K := FractionRing A
  let C := K ⊗[A] B
  obtain ⟨K', hK', aK', hfin, hsep, r, L, hL, aL, hfields, hsplit⟩ :=
    Algebra.exists_separable_extension_reduction_tensorProduct_equiv_pi K C
  let : Algebra A K' := Algebra.compHom K' (algebraMap A K)
  have : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨c0, hc0, S0, hS0, A0, hA0, hEt0, hFrac0, _, _, hsurj0⟩ :=
    exists_spread_finite_separable_extension A K K'
  obtain ⟨c, A', hA', aS', aA', hTower, hDomain, aFrac, hc, hfinite,
      hEtale, hFrac, hcover, D, hD, aD, aDL, aAL, hTDL, hTKL, hprops, hsplit'⟩ :=
    exists_spread_generic_product_domains A B K K' r L hsplit c0 hc0 S0 A0 hsurj0
  have : ∀ j, Module.Finite A' (D j) := fun j ↦ (hprops j).1
  have : ∀ j, IsDomain (D j) := fun j ↦ (hprops j).2.1
  have : ∀ j, IsFractionRing (D j) (L j) := fun j ↦ (hprops j).2.2
  have hinj : ∀ j, Function.Injective (algebraMap A' (D j)) := fun j ↦
    algebraMap_injective_of_field_isFractionRing A' (D j) K' (L j)
  let : ∀ j, Algebra (Localization.Away c) (D j) :=
    fun j ↦ Algebra.compHom (D j) (algebraMap (Localization.Away c) A')
  have : ∀ j, IsScalarTower (Localization.Away c) A' (D j) :=
    fun j ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsDomain (Localization.Away c) := Localization.Away.isDomain hc
  have : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away c) A'))) := by
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hEtale)
  have hlocal : ∀ j, ∃ s : Localization.Away c, s ≠ 0 ∧
      (topologically IsHomeomorph).universally
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom (Localization.Away c) A' (D j))
            (AlgHom.id (Localization.Away c) (Localization.Away s))).toRingHom)) := by
    intro j
    have : Module.Finite K' (L j) := (hfields j).1
    have : IsPurelyInseparable K' (L j) := (hfields j).2
    obtain ⟨s, hs, _, _, hhomeo⟩ := exists_spread_purely_inseparable_factors
      (Localization.Away c) A' (D j) (FractionRing (Localization.Away c)) K' (L j)
    exact ⟨s, hs, hhomeo⟩
  choose s hs hhomeo using hlocal
  obtain ⟨d, A'', hA'', aS'', aA'', hT'', hd, hfin'', hEt'', hcover'',
      E, hE, aE, hEprops, hsplit''⟩ :=
    exists_refinement_of_finite_domain_splitting A B c hc A' hcover r D hinj hsplit' s hs hhomeo
  refine ⟨d, A'', hA'', aS'', aA'', hT'', hd, hfin'', hEt'', hcover'',
    r, E, hE, aE, ?_, hsplit''⟩
  intro j
  obtain ⟨hfiniteE, hdomainE, hsurjE, hhomeoE⟩ := hEprops j
  refine ⟨hfiniteE, hdomainE, ?_, hsurjE, hhomeoE⟩
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfiniteE)

