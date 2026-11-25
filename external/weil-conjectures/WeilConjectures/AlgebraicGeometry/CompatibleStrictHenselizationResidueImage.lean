/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial

/-! # Lifting compatible residue embeddings through strict henselizations

Source: Stacks Project, Tags 04GU and 04HX.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry
open Scheme Etale

/-- The image of the first strict-henselization residue field lies in the second.
Source: Stacks Project, Tag 04HX and the residue inclusion in the proof of Tag 095T.
(blueprint: lem-weil-pbc-compatible-strict-henselization-residue-image).

Proof: choose affine neighbourhoods of the images of σ and τ. Identify their pointed
neighbourhood colimits with etale residue triples using Scheme.etale_local_ring_triples,
and use Scheme.strictHenselization_triples to identify
the model residue fields with separable closures of the point residue fields.
The factorization equalities force the embeddings given by ρA and ρB to extend
the point residue embeddings into k and k'. This assertion concerns their images,
so it is invariant under changing the residue identifications by base automorphisms.
The image under ι of an element in the first separable closure is separable algebraic
over the residue field of S. The residue map induced by g and hι makes it separable
algebraic over the residue field of T as well: a separable polynomial remains
separable after extending coefficients. Its image belongs to the second separable
closure. Indeed, every separable polynomial over that base field splits in κB,
and injectivity of κB → k' ensures all its roots in k' occur in that image.
Transport through the affine model isomorphisms to obtain the stated containment.
This step constructs no ring map A → B and uses no lifting theorem. -/
theorem Etale.compatibleStrictHenselization_residue_image
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
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
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    : ∀ x : IsLocalRing.ResidueField A,
      ∃ y : IsLocalRing.ResidueField B,
        (Spec.preimage ρB).hom y = (Spec.preimage (ι ≫ ρA)).hom x := by
  intro x
  obtain ⟨p, hp, hsep, hroot⟩ :=
    Etale.compatibleStrictHenselization_residue_separable_polynomial
      σ τ ι hι ν eA eB ρA ρB hρA hρB x
  apply (IsSepClosed.splits_of_separable p hsep).mem_range_of_isRoot hp
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hroot

end AlgebraicGeometry
