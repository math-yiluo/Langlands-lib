/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FiniteOverField
import WeilConjectures.RingTheory.SemilocalFiberGenerators

/-!
# Degree estimate for a tower finite over a field

Source: Stacks Project, Morphisms, proof of Tag 03J6, algebraic dimension estimate.
(blueprint: lem-weil-pbc-finite-field-tower-degree-bound).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree of a finite tower over a field is bounded using the fibre degrees
of its first map.

Source: Stacks Project, Morphisms, proof of Tag 03J6, the argument after writing
`X_z = Spec A` and `Y_z = Spec B`.
(blueprint: lem-weil-pbc-finite-field-tower-degree-bound)

Proof: Both schemes are affine because their structure morphisms are finite. Put
`B = Γ(Y, ⊤)` and `A = Γ(X, ⊤)`, with the compatible algebra structures induced by
`g` and `f`. Decompose the Artinian algebra `B` into its local factors `B_i`.
The affine pullback formula identifies the fibre at the corresponding point with
`Spec (A_i / m_i A_i)`, where `A_i = A ⊗[B] B_i` and `m_i` is the maximal ideal
of `B_i`. Its residue-field dimension is at most `n` by the hypothesis. Lift a basis
of that quotient to `A_i`. Since `m_i` is nilpotent, Nakayama gives a surjection
from at most `n` copies of `B_i` onto `A_i`. Restrict scalars to `K` and compare
dimensions. Summing over the finite set of factors gives the claimed inequality.
The empty target corresponds to the zero ring and empty product, giving `0 ≤ 0`.
For `n = 0`, Nakayama makes every `A_i` zero, so the estimate still holds. -/
theorem finrankΓ_comp_le_mul_of_finite {X Y : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) [IsFinite f] [IsFinite g] (n : ℕ)
    (hf : ∀ y, (f.fiberToSpecResidueField y).finrankΓ ≤ n) :
    (f ≫ g).finrankΓ ≤ n * g.finrankΓ := by
  classical
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : IsAffine X := isAffine_of_isAffineHom (f ≫ g)
  let := g.ΓAlgebra
  let := f.appTop.hom.toAlgebra
  let := (f ≫ g).ΓAlgebra
  have : IsScalarTower K Γ(Y, ⊤) Γ(X, ⊤) := by
    apply IsScalarTower.of_algebraMap_eq
    intro k
    rfl
  have : Module.Finite K Γ(Y, ⊤) := by
    have := finite_sections_top_of_isFinite g
    rwa [Scheme.Hom.appLE_top_top] at this
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : IsArtinianRing Γ(Y, ⊤) := .of_finite K Γ(Y, ⊤)
  have hb : ∀ p : MaximalSpectrum Γ(Y, ⊤), p.asIdeal.fiberDegree Γ(X, ⊤) ≤ n := by
    intro p
    let s := Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)))
    have sq : IsPullback X.isoSpec.inv s f Y.isoSpec.inv :=
      IsPullback.of_horiz_isIso ⟨by
        change X.isoSpec.inv ≫ f = Spec.map f.appTop ≫ Y.isoSpec.inv
        rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.isoSpec_hom_naturality,
          Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
    change p.toPrimeSpectrum.asIdeal.fiberDegree Γ(X, ⊤) ≤ n
    rw [← Scheme.Hom.fiberDegree_SpecMap Γ(Y, ⊤) Γ(X, ⊤) p.toPrimeSpectrum]
    exact (f.fiberDegree_of_isPullback sq p.toPrimeSpectrum).trans_le
      (hf (Y.isoSpec.inv p.toPrimeSpectrum))
  obtain ⟨q, hq⟩ := RingTheory.exists_surjective_fin_of_fiberDegree_le
    Γ(Y, ⊤) Γ(X, ⊤) n hb
  have hdim := LinearMap.finrank_le_finrank_of_surjective (f := q.restrictScalars K) hq
  simpa only [Scheme.Hom.finrankΓ, Module.finrank_pi_fintype, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] using hdim


end AlgebraicGeometry.Scheme.Hom
