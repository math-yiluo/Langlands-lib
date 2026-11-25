/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomialCore
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # Separable polynomials for compatible strict-henselization residues

Source: Stacks Project, Tags 04HX and 095T.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry
open Scheme Etale

/-- Each image element of the first strict-henselization residue field satisfies a
nonzero separable polynomial with coefficients in the second residue field.
Source: Stacks Project, Tag 04HX and the residue-field inclusion argument of Tag 095T.
(blueprint: lem-weil-pbc-compatible-strict-henselization-residue-polynomial).

Proof: put s = image(σ) and t = image(τ); hι gives g(t) = s. Choose affine
charts at s and t. The pointed-neighbourhood and residue-triples colimit identifications
identify κA with a separable closure of F = κ(s), compatibly with the structural map
F → κA, and identify the structural residue map G = κ(t) → κB. These are the maps
induced by the composites of the closed-point inclusions, eA or eB, and their structural
maps. The maps ρA and ρB extend these base residue maps by hρA and hρB.
Write a : κA → k' and b : κB → k' for the homomorphisms in the conclusion, and write
c : F → G for the residue map induced by g. Naturality of residue maps and hι give
  a.comp (F → κA) = b.comp ((G → κB).comp c).
Choose the monic separable minimal polynomial q of x over F. Put p equal to q with
coefficients mapped by F → G → κB. This coefficient homomorphism is injective, so p
is nonzero (also monic); Polynomial.Separable.map preserves separability. The displayed
compatibility gives p.eval₂ b (a x) = a (q.eval₂ (F → κA) x) = 0. Transporting through
the affine model identifications preserves this compatibility: no identification of
the entire field embeddings ρA or ρB with the embeddings into Ω is required.
This proves the polynomial assertion without assuming κB is separably closed. Splitting
p and obtaining a preimage are separate steps in the residue-image theorem. No data is
defined by choosing the polynomial witness from this unproved theorem.
-/
theorem Etale.compatibleStrictHenselization_residue_separable_polynomial
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ) :
    ∀ x : IsLocalRing.ResidueField A,
      ∃ p : Polynomial (IsLocalRing.ResidueField B),
        p ≠ 0 ∧ p.Separable ∧
          p.eval₂ (Spec.preimage ρB).hom ((Spec.preimage (ι ≫ ρA)).hom x) = 0 := by
  let algebra : Algebra (IsLocalRing.ResidueField B) k' :=
    (Spec.preimage ρB).hom.toAlgebra
  have hs := Etale.compatibleStrictHenselization_residue_isSeparable
    σ τ ι hι ν eA eB ρA ρB hρA hρB rfl
  intro x
  exact @exists_separable_polynomial_of_isSeparable _ _ _ _ algebra
    (Spec.preimage ρB).hom rfl _ (hs x)

end AlgebraicGeometry
