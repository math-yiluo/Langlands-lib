/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale
/-- Construction of compatible strict henselization data from pointed affine etale neighbourhoods.
Source: Stacks Tags 04HX, 03PS, 04GU, 04DY. (blueprint:
proposition-proper-base-change-projective-line--1)

Proof: construct the coordinate-ring colimits of pointed affine etale neighbourhoods.
Tags 04HX and 03PS identify these colimits with strict henselizations and their residue
fields. Functoriality from Tag 04GU gives the local map, structural equality, and residue
factorizations. Tag 04DY gives universal homeomorphisms on residue spectra.
-/
theorem Etale.exists_compatibleStrictHenselizationCoreData
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ)
    (ν : Spec (.of Ω) ⟶ Spec (.of k')) :
    let s := ν ≫ ι ≫ σ
    let t := ν ≫ τ
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (eA : Spec (.of A) ≅ strictLocalization s)
              (eB : Spec (.of B) ≅ strictLocalization t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
                strictLocalizationToBase s =
                eB.hom ≫ strictLocalizationToBase t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictLocalizationToBase s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictLocalizationToBase t = τ := by
  dsimp
  obtain ⟨A, B, cA, cB, hA, hB, sA, sB, eA, eB, ρA, ρB, hUA, hUB, ha0, hb0⟩ :=
    Etale.exists_compatibleStrictHenselizationCoreExistence σ τ ι hι hσ hτ ν
  let := cA
  let := cB
  let := hA
  let := hB
  let := sA
  let := sB
  obtain ⟨φ, hφ, hbase⟩ :=
    Etale.exists_compatibleStrictHenselizationCoreCompletion
      (by simpa only [Category.assoc] using congrArg (ν ≫ ·) hι) eA eB
  exact ⟨A, B, cA, cB, hA, hB, sA, sB, φ, hφ, eA, eB, ρA, ρB, hUA, hUB,
    hbase, ha0, hb0⟩
end AlgebraicGeometry
