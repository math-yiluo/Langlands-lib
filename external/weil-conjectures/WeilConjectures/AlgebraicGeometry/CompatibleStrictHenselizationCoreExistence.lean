/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale
private theorem integral_point_residue
    {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo σ)).hom.IsIntegral := by
  obtain ⟨s, ψ, hψ, hfac⟩ := hσ
  have hs : σ (IsLocalRing.closedPoint k) = s := by
    rw [← hfac, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  subst s
  have heq : Scheme.descResidueField (Scheme.stalkClosedPointTo σ) = ψ := by
    apply Spec.map_injective
    apply (cancel_mono (S.fromSpecResidueField (σ (IsLocalRing.closedPoint k)))).mp
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S σ).trans
      hfac.symm
  rw [heq]
  exact hψ

private theorem integral_point_embedding
    {S : Scheme.{u}} {k Ω : Type u} [Field k] [Field Ω]
    (σ : Spec (.of k) ⟶ S) (ν : Spec (.of Ω) ⟶ Spec (.of k))
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ) :
    ∃ b : S.residueField ((ν ≫ σ) (IsLocalRing.closedPoint Ω)) ⟶ .of k,
      b.hom.IsIntegral ∧
      b ≫ Spec.preimage ν = Scheme.descResidueField (Scheme.stalkClosedPointTo (ν ≫ σ)) := by
  have hx : (ν ≫ σ) (IsLocalRing.closedPoint Ω) = σ (IsLocalRing.closedPoint k) := by
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  obtain ⟨b, hb, hfac⟩ :
      ∃ b : S.residueField ((ν ≫ σ) (IsLocalRing.closedPoint Ω)) ⟶ .of k,
        b.hom.IsIntegral ∧
        Spec.map b ≫ S.fromSpecResidueField ((ν ≫ σ) (IsLocalRing.closedPoint Ω)) = σ := by
    rw [hx]
    exact ⟨Scheme.descResidueField (Scheme.stalkClosedPointTo σ),
      integral_point_residue σ hσ,
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S σ⟩
  refine ⟨b, hb, ?_⟩
  apply Spec.map_injective
  apply (cancel_mono (S.fromSpecResidueField ((ν ≫ σ) (IsLocalRing.closedPoint Ω)))).mp
  rw [Spec.map_comp, Category.assoc, hfac, Spec.map_preimage]
  exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω S (ν ≫ σ)).symm

private theorem integral_separable_embedding
    {F E k Ω : Type u} [Field F] [Field E] [Field k] [IsSepClosed k] [Field Ω]
    [Algebra F E] [Algebra.IsSeparable F E]
    (b : F →+* k) (hb : b.IsIntegral) (β : k →+* Ω) (c : E →+* Ω)
    (hc : c.comp (algebraMap F E) = β.comp b) :
    ∃ η : E →+* k, η.IsIntegral ∧ β.comp η = c := by
  obtain ⟨η, hη⟩ := RingHom.exists_comp_eq_of_isSepClosed b β c hc
  have hbη : η.comp (algebraMap F E) = b := by
    ext x
    apply β.injective
    have h := congrArg (fun f : F →+* Ω ↦ f x) hc
    simpa only [RingHom.comp_apply, ← hη] using h
  refine ⟨η, ?_, hη⟩
  intro x
  have h := hb x
  rw [← hbη] at h
  exact h.of_comp

set_option backward.isDefEq.respectTransparency false in
private theorem integral_strictHenselization_residue
    {S : Scheme.{u}} {k Ω : Type u} [Field k] [IsSepClosed k]
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (ν : Spec (.of Ω) ⟶ Spec (.of k))
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (s : Spec (.of Ω) ⟶ S) (hs : ν ≫ σ = s) :
    ∃ hA : HenselianLocalRing (strictHenselization s),
      letI := hA
      ∃ sA : IsSepClosed (IsLocalRing.ResidueField (strictHenselization s)),
        letI := sA
        ∃ ρ : Spec (.of k) ⟶
            Spec (.of (IsLocalRing.ResidueField (strictHenselization s))),
          IsUniversalHomeomorphism ρ ∧
          ρ ≫ Spec.map (CommRingCat.ofHom
            (IsLocalRing.residue (strictHenselization s))) ≫
            strictLocalizationToBase s = σ := by
  subst s
  classical
  let s := ν ≫ σ
  let F := S.residueField (s (IsLocalRing.closedPoint Ω))
  let α := (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom
  let : Algebra F Ω := α.toAlgebra
  obtain ⟨hlocal, hstrict, _, _, δ, ⟨_, hbase⟩, _⟩ := strictHenselizationResidue s rfl
  let := hlocal
  let := hstrict
  let E := separableClosure F Ω
  let c := (IntermediateField.val E).toRingHom
  let β := Spec.preimage ν
  obtain ⟨b, hb, hcomp⟩ := integral_point_embedding σ ν hσ
  have hc : c.comp (algebraMap F E) = β.hom.comp b.hom := by
    exact (congrArg CommRingCat.Hom.hom hcomp).symm
  obtain ⟨η, hη, hηβ⟩ := integral_separable_embedding b.hom hb β.hom c hc
  let γ := η.comp δ.toRingHom
  have hγ : γ.IsIntegral :=
    RingHom.IsIntegral.trans δ.toRingHom η
      (RingHom.isIntegral_of_surjective δ.toRingHom δ.surjective) hη
  let : Algebra (IsLocalRing.ResidueField (strictHenselization s)) k := γ.toAlgebra
  have : Algebra.IsIntegral (IsLocalRing.ResidueField (strictHenselization s)) k := ⟨hγ⟩
  have : IsPurelyInseparable (IsLocalRing.ResidueField (strictHenselization s)) k :=
    inferInstance
  let ρ := Spec.map (CommRingCat.ofHom γ)
  have hρ : IsUniversalHomeomorphism ρ := by
    change IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom
      (algebraMap (IsLocalRing.ResidueField (strictHenselization s)) k)))
    infer_instance
  refine ⟨inferInstance, inferInstance, ρ, hρ, ?_⟩
  let : Algebra k Ω := β.hom.toAlgebra
  have hflat : Flat ν := by
    rw [← Spec.map_preimage ν, Flat.SpecMap_iff]
    change Module.Flat k Ω
    infer_instance
  have hsurj : Surjective ν := ⟨fun x ↦ ⟨IsLocalRing.closedPoint Ω,
    Subsingleton.elim _ _⟩⟩
  have : Epi ν := Flat.epi_of_flat_of_surjective ν
  apply (cancel_epi ν).mp
  have hring : β.hom.comp γ = c.comp δ.toRingHom := by
    change β.hom.comp (η.comp δ.toRingHom) = _
    rw [← RingHom.comp_assoc, hηβ]
  have hmap : ν ≫ ρ = Spec.map (CommRingCat.ofHom (c.comp δ.toRingHom)) := by
    rw [← Spec.map_preimage ν]
    change Spec.map β ≫ Spec.map (CommRingCat.ofHom γ) = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hring)
  rw [← Category.assoc ν ρ, hmap]
  simpa only [← Spec.map_comp_assoc, CommRingCat.ofHom_comp] using hbase

/-- The strict henselization rings and residue maps exist for the two geometric points.
Source: Stacks Project, Tags 04HX, 03PS and 04DY.
(blueprint: compatible-strict-henselization-core-existence)
Proof: take A and B to be the actual coordinate-ring colimits strictHenselization
of the indicated geometric points, with eA and eB the identity spectrum isomorphisms.
By affine neighbourhood cofinality and Tag 04HX, these colimits are the strict
henselizations of the local rings at the images of σ and τ. Their residue fields are
the separable algebraic closures of the respective point residue fields inside Ω;
they are henselian local rings with separably closed residue fields. The integral
factorizations hσ and hτ identify k and k' as algebraic extensions of those point
residue fields. Since k and k' are separably closed, their embeddings into Ω contain
these separable closures. The remaining extensions are algebraic purely inseparable:
an algebraic extension of a separably closed field has no nontrivial separable part.
Take ρA and ρB to be the spectra of these residue inclusions. Purely inseparable
algebraic field extensions give integral, radicial, surjective spectrum maps, hence
universal homeomorphisms. The inclusions extend the given point residue maps, so
composition with the ring residue maps and the colimit structural maps gives σ and τ.
No ring data are chosen from a mere unproved existence assertion. -/
theorem Etale.exists_compatibleStrictHenselizationCoreExistence
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
          ∃ (eA : Spec (.of A) ≅ strictLocalization s)
            (eB : Spec (.of B) ≅ strictLocalization t)
            (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
            (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
            IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
            ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
              eA.hom ≫ strictLocalizationToBase s = σ ∧
            ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
              eB.hom ≫ strictLocalizationToBase t = τ := by
  have _ := hι
  dsimp
  have hresA := integral_strictHenselization_residue σ (ν ≫ ι) hσ
    (ν ≫ ι ≫ σ) (Category.assoc ν ι σ)
  obtain ⟨hA, sA, ρA, hUA, ha⟩ := hresA
  obtain ⟨hB, sB, ρB, hUB, hb⟩ := integral_strictHenselization_residue τ ν hτ (ν ≫ τ) rfl
  let := hA
  let := hB
  let := sA
  let := sB
  refine ⟨strictHenselization (ν ≫ ι ≫ σ), strictHenselization (ν ≫ τ),
    inferInstance, inferInstance, hA, hB, sA, sB, Iso.refl _, Iso.refl _,
    ρA, ρB, hUA, hUB, ?_, ?_⟩
  · simpa only [Iso.refl_hom, Category.id_comp, Category.assoc] using ha
  · simpa only [Iso.refl_hom, Category.id_comp] using hb
end AlgebraicGeometry
