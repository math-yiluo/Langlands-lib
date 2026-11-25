/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale

/-! # Lifting compatible residue embeddings through strict henselizations

Source: Stacks Project, Tags 04GU and 04HX.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open Scheme Etale

set_option backward.isDefEq.respectTransparency false in
private theorem lift_indEtale_residue
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsLocalRing A] [HenselianLocalRing B]
    [Algebra.IndEtale R A]
    (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B)
    (hr : (IsLocalRing.residue B).comp (algebraMap R B) =
      r.comp ((IsLocalRing.residue A).comp (algebraMap R A))) :
    ∃ f : A →ₐ[R] B,
      (IsLocalRing.residue B).comp f.toRingHom = r.comp (IsLocalRing.residue A) := by
  classical
  let q := IsLocalRing.maximalIdeal A
  let m := IsLocalRing.maximalIdeal B
  let p := q.comap (algebraMap R A)
  let eA : IsLocalRing.ResidueField A ≃+* q.ResidueField :=
    RingEquiv.ofBijective (algebraMap (A ⧸ q) q.ResidueField)
      q.bijective_algebraMap_quotient_residueField
  let eB : IsLocalRing.ResidueField B ≃+* m.ResidueField :=
    RingEquiv.ofBijective (algebraMap (B ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  have heA (x : A) : eA (IsLocalRing.residue A x) = algebraMap A q.ResidueField x := rfl
  have heB (x : B) : eB (IsLocalRing.residue B x) = algebraMap B m.ResidueField x := rfl
  have hm : p = m.comap (algebraMap R B) := by
    ext x
    change algebraMap R A x ∈ q ↔ algebraMap R B x ∈ m
    rw [← IsLocalRing.residue_eq_zero_iff (R := A),
      ← IsLocalRing.residue_eq_zero_iff (R := B)]
    have h := DFunLike.congr_fun hr x
    change IsLocalRing.residue B (algebraMap R B x) =
      r (IsLocalRing.residue A (algebraMap R A x)) at h
    rw [h]
    constructor
    · intro hz
      rw [hz, map_zero]
    · intro hz
      exact r.injective (hz.trans (map_zero r).symm)
  let τ := eB.toRingHom.comp (r.comp eA.symm.toRingHom)
  have hτ : τ.comp (Ideal.ResidueField.map p q (algebraMap R A) rfl) =
      Ideal.ResidueField.map p m (algebraMap R B) hm := by
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    change eB (r (eA.symm (algebraMap A q.ResidueField (algebraMap R A x)))) =
      algebraMap B m.ResidueField (algebraMap R B x)
    rw [← heA, eA.symm_apply_apply, ← heB]
    exact congrArg eB (DFunLike.congr_fun hr x).symm
  obtain ⟨I, hI, hfiltered, P, hEtale⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := R) (S := A)
  let : SmallCategory I := hI
  let : IsFiltered I := hfiltered
  have : HasColimit P.diag := ⟨⟨P.cocone, P.isColimit⟩⟩
  obtain ⟨f, ⟨hf, hred⟩, -⟩ := Algebra.map_into_henselian_colimit R B A I P.diag
    ⟨(colimit.isColimit P.diag).coconePointUniqueUpToIso P.isColimit⟩
    hEtale q p rfl hm τ hτ
  refine ⟨f, ?_⟩
  ext x
  change IsLocalRing.residue B (f x) = r (IsLocalRing.residue A x)
  apply eB.injective
  rw [heB]
  have h := DFunLike.congr_fun hred (algebraMap A q.ResidueField x)
  rw [Ideal.ResidueField.map_algebraMap] at h
  change algebraMap B m.ResidueField (f x) =
    eB (r (eA.symm (algebraMap A q.ResidueField x))) at h
  simpa only [← heA, eA.symm_apply_apply] using h

set_option backward.isDefEq.respectTransparency false in
/-- Lift compatible geometric residue embeddings to a ring map of strict henselizations.
Source: Stacks Project, Tags 04GU and 04HX.
(blueprint: lem-weil-pbc-compatible-strict-henselization-residue-lift).

Proof: choose an affine open U = Spec R containing the image of σ. The closed
point of Spec B maps into U, so the entire local spectrum Spec B maps into U:
every point generalizes its closed point. This gives the base ring map R → B.
Use Scheme.etale_local_ring_triples to identify the pointed neighbourhood
colimit over U with the etale residue-triples diagram. Scheme.strictHenselization_triples
identifies its residue field with the chosen separable closure and its maximal ideal
with the pointed prime. Transport this colimit presentation along eA using full
faithfulness of Spec. Thus A is an ind-etale R-algebra with its maximal ideal over
the inverse image of the maximal ideal of B. The supplied hres, followed by the two
factorization equalities and hι, says that r respects the base residue field.
Apply Algebra.map_into_henselian_colimit (Tag 08HR, the lifting property used in
Tag 04GU) with this maximal ideal and r. Identify the prime residue fields there
with the local residue fields here. Its prescribed reduction gives the ring residue
diagram; its R-algebra compatibility gives the equality of maps to U and hence the
structural square after composing with U → S. Only φ is obtained: r and its spectral
compatibility are inputs, constructed independently by the caller. -/
theorem Etale.exists_compatibleStrictHenselizationResidueLift
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
    (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B)
    (hres : ρB ≫ Spec.map (CommRingCat.ofHom r) = ι ≫ ρA) :
    ∃ (φ : A →+* B),
      (IsLocalRing.residue B).comp φ = r.comp (IsLocalRing.residue A) ∧
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictLocalizationToBase (ν ≫ ι ≫ σ) =
        eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g := by
  classical
  let jA := eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)
  let jB := eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g
  obtain ⟨R, i, hi, hσ, -⟩ :=
    exists_affine_mem_range_and_range_subset
      (show σ (IsLocalRing.closedPoint k) ∈ (⊤ : S.Opens) from trivial)
  have := hi
  have hclosedA : jA (IsLocalRing.closedPoint A) = σ (IsLocalRing.closedPoint k) := by
    have h := congrArg (fun f : Spec (.of k) ⟶ S ↦ f (IsLocalRing.closedPoint k)) hρA
    change jA (PrimeSpectrum.comap (IsLocalRing.residue A)
      (ρA (IsLocalRing.closedPoint k))) = σ (IsLocalRing.closedPoint k) at h
    rwa [IsLocalRing.PrimeSpectrum.comap_residue] at h
  have hclosedB : jB (IsLocalRing.closedPoint B) = σ (IsLocalRing.closedPoint k) := by
    have h := congrArg (fun f : Spec (.of k') ⟶ S ↦ f (IsLocalRing.closedPoint k'))
      ((congrArg (fun f ↦ f ≫ g) hρB).trans hι.symm)
    change jB (PrimeSpectrum.comap (IsLocalRing.residue B)
      (ρB (IsLocalRing.closedPoint k'))) = σ (ι (IsLocalRing.closedPoint k')) at h
    rwa [IsLocalRing.PrimeSpectrum.comap_residue,
      Subsingleton.elim (ι (IsLocalRing.closedPoint k')) (IsLocalRing.closedPoint k)] at h
  have hA : Set.range jA ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map jA.continuous).mem_open
      i.opensRange.isOpen (by simpa only [hclosedA] using hσ)
  have hB : Set.range jB ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map jB.continuous).mem_open
      i.opensRange.isOpen (by simpa only [hclosedB] using hσ)
  let a : R →+* A := (Spec.preimage (IsOpenImmersion.lift i jA hA)).hom
  let b : R →+* B := (Spec.preimage (IsOpenImmersion.lift i jB hB)).hom
  have ha : Spec.map (CommRingCat.ofHom a) ≫ i = jA := by
    rw [show CommRingCat.ofHom a = Spec.preimage (IsOpenImmersion.lift i jA hA) from rfl,
      Spec.map_preimage]
    exact IsOpenImmersion.lift_fac i jA hA
  have hb : Spec.map (CommRingCat.ofHom b) ≫ i = jB := by
    rw [show CommRingCat.ofHom b = Spec.preimage (IsOpenImmersion.lift i jB hB) from rfl,
      Spec.map_preimage]
    exact IsOpenImmersion.lift_fac i jB hB
  let : Algebra R A := a.toAlgebra
  let : Algebra R B := b.toAlgebra
  have hs : (ν ≫ ι ≫ σ) (IsLocalRing.closedPoint Ω) ∈ Set.range i := by
    simpa only [Scheme.Hom.comp_apply,
      Subsingleton.elim (ι (ν (IsLocalRing.closedPoint Ω))) (IsLocalRing.closedPoint k)]
      using hσ
  have : Algebra.IndEtale R A :=
    strictHenselization_indEtale_of_affine_chart (ν ≫ ι ≫ σ) R i hs eA a ha
  have hspec :
      ρB ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue B).comp b)) =
      ρB ≫ Spec.map (CommRingCat.ofHom
        (r.comp ((IsLocalRing.residue A).comp a))) := by
    apply (cancel_mono i).mp
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    calc
      ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
          Spec.map (CommRingCat.ofHom b) ≫ i = τ ≫ g := by
        rw [hb]
        simpa only [jB, Category.assoc] using congrArg (fun f ↦ f ≫ g) hρB
      _ = ι ≫ σ := hι.symm
      _ = ρB ≫ Spec.map (CommRingCat.ofHom r) ≫
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
          Spec.map (CommRingCat.ofHom a) ≫ i := by
        rw [ha, ← Category.assoc ρB, hres]
        simpa only [jA, Category.assoc] using congrArg (fun f ↦ ι ≫ f) hρA.symm
  have hbase : (IsLocalRing.residue B).comp b =
      r.comp ((IsLocalRing.residue A).comp a) := by
    let t := (Spec.preimage ρB).hom
    have ht : Spec.map (CommRingCat.ofHom t) = ρB := Spec.map_preimage ρB
    rw [← ht, ← Spec.map_comp, ← Spec.map_comp] at hspec
    have h := congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)
    ext x
    exact t.injective (DFunLike.congr_fun h x)
  obtain ⟨f, hf⟩ := lift_indEtale_residue R A B r hbase
  refine ⟨f.toRingHom, hf, ?_⟩
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ jA = jB
  rw [← ha, ← Category.assoc, ← Spec.map_comp]
  have hfbase : CommRingCat.ofHom a ≫ CommRingCat.ofHom f.toRingHom =
      CommRingCat.ofHom b := by
    ext x
    exact f.commutes x
  rw [hfbase, hb]

end AlgebraicGeometry
