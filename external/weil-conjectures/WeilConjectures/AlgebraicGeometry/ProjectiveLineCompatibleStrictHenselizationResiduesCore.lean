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
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreData
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift

/-! # Compatible strict henselizations and geometric residue maps

Source: Stacks Project, Tags 04HX, 03PS, 04GU and 095T.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Core data for compatible strict henselizations to the
original integral geometric points. The residue maps are universal homeomorphisms.

Source: Stacks Project, Tags 04HX and 03PS, functoriality Tag 04GU, and the last two
paragraphs of the proof of Tag 095T; topological invariance Tag 04DY.
(blueprint: compatible-strict-henselization-residues-core).

Proof: take the coordinate-ring colimits of the affine pointed neighbourhoods at
s and t, and use their spectra for eA and eB. Tag 04HX identifies each as a strictly
henselian local ring and identifies
its residue field with the relative separable closure of the base residue field
inside Ω. Since k and k' are separably closed, these relative separable closures
already lie in k and k', respectively: a separable polynomial splits there, so
all of its roots in Ω lie in the image of that field. This gives ρA and ρB.
The integral factorizations hσ and hτ make k and k' algebraic over their base
residue fields. Their extensions of the relative separable closures are thus
purely inseparable, and their spectra are universal homeomorphisms. The pointed
factorization in Tag 04HX proves the two displayed geometric-point equalities.
The equality hι identifies the base-residue embeddings into Ω. Functoriality of
strict henselization (Tags 03PS and 04GU) gives the local ring map φ, the structural
square, and the commuting residue square. Equality can be checked after embedding
both residue fields into Ω; those embeddings are injective. No sheaf, cohomology,
or closed-fibre comparison is used. -/
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues_core
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
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictLocalizationToBase s =
                eB.hom ≫ strictLocalizationToBase t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictLocalizationToBase s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictLocalizationToBase t = τ ∧
              True := by
  dsimp
  obtain ⟨A, B, cA, cB, hA, hB, sA, sB, φ, hφ, eA, eB, ρA, ρB,
      hUA, hUB, hbase, hρA, hρB⟩ :=
    Etale.exists_compatibleStrictHenselizationCoreData σ τ ι hι hσ hτ ν
  exact ⟨A, B, cA, cB, hA, hB, sA, sB, φ, hφ, eA, eB, ρA, ρB,
    hUA, hUB, hbase, hρA, hρB, True.intro⟩

/-- A compatible local map can be chosen to induce the specified geometric residue square.
Source: Stacks Project, Tags 04GU and 04HX.
(blueprint: proposition-proper-base-change-projective-line--1).

Proof: first use residue-image containment to construct the unique embedding r whose
composite with the injective map κB → k' equals κA → k → k'. Prove its ring laws
by injectivity and prove hres by full faithfulness of Spec. Then lift r through the
strict henselization universal
property. The commuting ring residue diagram makes the lift local, since field embeddings
and residue projections are local. Surjectivity of the residue projection identifies the
chosen residue map with the induced residue map of the lift. This asserts existence of a
compatible map, rather than compatibility of every independently chosen map. -/
theorem Etale.compatibleStrictHenselization_residue_square
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
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ) :
    ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
      letI := hφ
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictLocalizationToBase (ν ≫ ι ≫ σ) =
        eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g ∧
      ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) =
        ι ≫ ρA := by
  classical
  let a := (Spec.preimage (ι ≫ ρA)).hom
  let b := (Spec.preimage ρB).hom
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice
    (Etale.compatibleStrictHenselization_residue_image σ τ ι hι ν eA eB ρA ρB hρA hρB)
  let r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B :=
    { toFun := f
      map_one' := b.injective (by rw [hf, a.map_one, b.map_one])
      map_mul' := fun x y ↦ b.injective (by rw [hf, b.map_mul, hf, hf, a.map_mul])
      map_zero' := b.injective (by rw [hf, a.map_zero, b.map_zero])
      map_add' := fun x y ↦ b.injective (by rw [hf, b.map_add, hf, hf, a.map_add]) }
  have hbr : b.comp r = a := by
    ext x
    exact hf x
  have hres : ρB ≫ Spec.map (CommRingCat.ofHom r) = ι ≫ ρA := by
    rw [← Spec.map_preimage ρB, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (b.comp r)) = _
    rw [hbr]
    exact Spec.map_preimage (ι ≫ ρA)
  obtain ⟨φ, hcomm, hbase⟩ :=
    Etale.exists_compatibleStrictHenselizationResidueLift
      σ τ ι hι ν eA eB ρA ρB hρA hρB r hres
  haveI : IsLocalHom ((IsLocalRing.residue B).comp φ) := by
    rw [hcomm]
    infer_instance
  haveI : IsLocalHom φ := isLocalHom_of_comp φ (IsLocalRing.residue B)
  have hr : IsLocalRing.ResidueField.map φ = r := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
    exact DFunLike.congr_fun hcomm a
  refine ⟨φ, inferInstance, hbase, ?_⟩
  simpa only [hr] using hres

end AlgebraicGeometry
