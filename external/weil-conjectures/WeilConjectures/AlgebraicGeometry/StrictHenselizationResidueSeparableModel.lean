/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality

/-! # The residue field of a strict-henselization model

Source: Stacks Project, Tags 04HX and 04GP.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The closed point of any affine local model of the strict henselization factors
through a base residue field, over which its own residue field is separable.
Source: Stacks Project, Tag 04HX and Tag 04GP, property (5).
(blueprint: lem-weil-pbc-strict-henselization-residue-separable-model)

Proof: apply the existing `strictHenselizationResidue` theorem with the algebra
structure induced by z. It identifies the coordinate colimit's residue field with
the relative separable closure K of the base residue field F in Ω, and gives the
pointed structural factorization. The scheme isomorphism e gives a ring
isomorphism A to that coordinate colimit. Compose it with the surjection to K.
This surjection has maximal-ideal kernel and therefore gives a residue-field
isomorphism σA: κA ≃ K. Write d for σA followed by K's inclusion into Ω.
The pointed structural factorization transports to Spec(d) followed by the
closed-point structural morphism q of A, giving z. Thus q has image s, the image
of z. The field-point equivalence supplies f: κ(s) → κA with Spec(f) followed
by the canonical residue-field point equal to q. Cancellation of that canonical
monomorphism gives d composed with f equal to the geometric embedding of F.
Every d(x) belongs to K, hence is separable over F. Regard d as an F-algebra
homomorphism using this equality; `IsSeparable.of_algHom` descends separability
to x. All witnesses are eliminated within this theorem proof. -/
theorem strictHenselization_residue_separable_model
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    [HenselianLocalRing A]
    (z : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization z) :
    ∃ (s : S) (f : S.residueField s →+* IsLocalRing.ResidueField A),
      (letI := f.toAlgebra; ∀ x : IsLocalRing.ResidueField A,
        IsSeparable (S.residueField s) x) ∧
      Spec.map (CommRingCat.ofHom f) ≫ S.fromSpecResidueField s =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ e.hom ≫
          strictLocalizationToBase z := by
  classical
  let s := z (IsLocalRing.closedPoint Ω)
  let F := S.residueField s
  let : Algebra F Ω := (descResidueField (stalkClosedPointTo z)).hom.toAlgebra
  obtain ⟨hl, _, _, _, σ, hσ, _⟩ := AlgebraicGeometry.strictHenselizationResidue z rfl
  let := hl
  let C := strictHenselization z
  let K := separableClosure F Ω
  let ψ : C →+* K := σ.toRingHom.comp (IsLocalRing.residue C)
  let r : A →+* C := (Spec.preimage e.inv).hom
  let ri : CommRingCat.of A ≅ C :=
    { hom := Spec.preimage e.inv
      inv := Spec.preimage e.hom
      hom_inv_id := by
        apply Spec.map_injective
        simp only [Spec.map_comp, Spec.map_preimage, Iso.hom_inv_id, Spec.map_id]
      inv_hom_id := by
        apply Spec.map_injective
        simp only [Spec.map_comp, Spec.map_preimage, Iso.inv_hom_id, Spec.map_id] }
  have hr : Function.Surjective r := ri.commRingCatIsoToRingEquiv.surjective
  let ψA : A →+* K := ψ.comp r
  have hsurj : Function.Surjective ψA :=
    σ.surjective.comp ((IsLocalRing.residue_surjective (R := C)).comp hr)
  have hker := IsLocalRing.ker_eq_maximalIdeal ψA hsurj
  let σA : IsLocalRing.ResidueField A ≃+* K :=
    (Ideal.quotEquivOfEq hker.symm).trans (ψA.quotientKerEquivOfSurjective hsurj)
  have hσA : σA.toRingHom.comp (IsLocalRing.residue A) = ψA := by
    ext x
    rfl
  let d : IsLocalRing.ResidueField A →+* Ω := K.subtype.comp σA.toRingHom
  let q := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ e.hom ≫
    strictLocalizationToBase z
  have hd : Spec.map (CommRingCat.ofHom d) ≫ q = z := by
    dsimp only [q]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom d)), ← Spec.map_comp]
    have heq : CommRingCat.ofHom (IsLocalRing.residue A) ≫ CommRingCat.ofHom d =
        Spec.preimage e.inv ≫ CommRingCat.ofHom (K.subtype.comp ψ) := by
      apply CommRingCat.hom_ext
      change d.comp (IsLocalRing.residue A) = (K.subtype.comp ψ).comp r
      dsimp only [d]
      rw [RingHom.comp_assoc, hσA]
      rfl
    rw [heq, Spec.map_comp, Spec.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hval : K.subtype = (IntermediateField.val K).toRingHom := by
      ext x
      rfl
    rw [hval]
    simpa only [ψ, RingHom.comp_assoc] using hσ.2
  let t := SpecToEquivOfField (IsLocalRing.ResidueField A) S q
  have ht : t.1 = s := by
    have hh := congrArg (fun f : Spec (.of Ω) ⟶ S ↦ f (IsLocalRing.closedPoint Ω)) hd
    change q (Spec.map (CommRingCat.ofHom d) (IsLocalRing.closedPoint Ω)) = s at hh
    rw [Subsingleton.elim
      (Spec.map (CommRingCat.ofHom d) (IsLocalRing.closedPoint Ω))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A))] at hh
    exact hh
  let f : S.residueField s ⟶ CommRingCat.of (IsLocalRing.ResidueField A) :=
    (S.residueFieldCongr ht).inv ≫ t.2
  have hf : Spec.map f ≫ S.fromSpecResidueField s = q := by
    dsimp only [f]
    rw [Spec.map_comp, Category.assoc]
    change Spec.map t.2 ≫ Spec.map (S.residueFieldCongr ht.symm).hom ≫
      S.fromSpecResidueField s = q
    rw [residueFieldCongr_fromSpecResidueField]
    exact (SpecToEquivOfField (IsLocalRing.ResidueField A) S).symm_apply_apply q
  have hdf : d.comp f.hom = algebraMap F Ω := by
    suffices h : CommRingCat.ofHom (d.comp f.hom) =
        CommRingCat.ofHom (algebraMap F Ω) from congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    apply (cancel_mono (S.fromSpecResidueField s)).1
    rw [show CommRingCat.ofHom (d.comp f.hom) = f ≫ CommRingCat.ofHom d from rfl,
      Spec.map_comp, Category.assoc, hf, hd]
    exact (SpecToEquivOfField Ω S).symm_apply_apply z |>.symm
  refine ⟨s, f.hom, ?_, hf⟩
  let : Algebra F (IsLocalRing.ResidueField A) := f.hom.toAlgebra
  let a : IsLocalRing.ResidueField A →ₐ[F] Ω :=
    { d with commutes' := fun x ↦ DFunLike.congr_fun hdf x }
  intro x
  have hx : IsSeparable F (d x) :=
    mem_separableClosure_iff.mp (σA x).property
  exact IsSeparable.of_algHom F a hx


end AlgebraicGeometry.Scheme
