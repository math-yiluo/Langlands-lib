/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Morphisms from a field spectrum and residue fields

Source: Stacks Project, Schemes, discussion before Lemma 01J9, and Algebra,
Local rings and Proposition 00CT (blueprint: lem-weil-pbc-spec-field-point-residue-field).

## Main statements

* `spec_field_point_residue_field`: the affine residue field and its canonical ring map.
* `spec_field_point_residue_field_affine_open`: the affine-open factorization.
* `spec_field_point_residue_field_map`: the kernel point and unique residue-field extension.
* `spec_field_point_residue_field_generic`: the generic-point fraction-field case.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Stacks, Algebra, Local rings and 00CT; Schemes, discussion before 01J9
(blueprint: lem-weil-pbc-spec-field-point-residue-field), clause (1).

Proof: use `lem-weil-pbc-spec-residue-field-identification` to identify the scheme
residue field with the residue field of the localization, compatibly with the germ
and residue maps. Then `lem-weil-pbc-prime-residue-field-algebra` gives the kernel
and the fraction-field structure on the prime quotient. -/
theorem spec_field_point_residue_field
    (R : CommRingCat.{u}) (p : PrimeSpectrum R) :
    Nonempty ((Spec R).residueField p ≅
      CommRingCat.of (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))) ∧
    CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R p).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ p trivial ≫
        (Spec R).residue p ∧
    RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal ∧
    IsFractionRing (R ⧸ p.asIdeal) p.asIdeal.ResidueField := by
  refine ⟨⟨Scheme.Spec.residueFieldIso R p⟩, ?_, ?_, inferInstance⟩
  · exact Scheme.Spec.algebraMap_residueFieldIso_inv R p
  · exact Ideal.ker_algebraMap_residueField p.asIdeal

/-- Stacks, Schemes, discussion before 01J9 and its following diagram
(blueprint: lem-weil-pbc-spec-field-point-residue-field), clause (2).

Proof: `lem-weil-pbc-affine-open-spec-points` supplies the corresponding prime and
open immersion. Apply `lem-weil-pbc-residue-field-point-naturality`: the residue-field
map of the open immersion is an isomorphism, and the canonical point maps commute.
Use `lem-weil-pbc-spec-residue-field-identification` to replace the affine point map
by Spec of the canonical ring map. Invert the residue-field isomorphism and compose
contravariantly to obtain the asserted factorization. -/
theorem spec_field_point_residue_field_affine_open
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    ∃ (p : PrimeSpectrum Γ(X, U)) (hp : hU.fromSpec p = x)
      (e : X.residueField x ≅ CommRingCat.of p.asIdeal.ResidueField),
      e.hom = (X.residueFieldCongr hp).inv ≫ hU.fromSpec.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso Γ(X, U) p).hom ∧
      X.fromSpecResidueField x =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) p.asIdeal.ResidueField) ≫ e.inv) ≫
          hU.fromSpec := by
  have hx' : x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hx
  obtain ⟨p, rfl⟩ := hx'
  let e := asIso (hU.fromSpec.residueFieldMap p) ≪≫
    Scheme.Spec.residueFieldIso Γ(X, U) p
  refine ⟨p, rfl, e, ?_, ?_⟩
  · simp [e]
  · simp only [e, Iso.trans_inv, asIso_inv, Spec.map_comp, Category.assoc]
    rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc]
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField hU.fromSpec p]
    simp

/-- Stacks, Schemes, discussion before 01J9; Algebra, 00E2 and 00CT
(blueprint: lem-weil-pbc-spec-field-point-residue-field), clause (3).

Proof: Spec of a field has the unique prime zero. The point map is prime comap,
so its image ideal is the kernel (`def-weil-affine-spectrum`). Use
`lem-weil-pbc-morphism-from-spec-field` to factor the morphism through the image's
canonical residue-field point. Under `lem-weil-pbc-spec-residue-field-identification`,
full faithfulness of Spec says that the induced field map extends the given ring map.
By clause (1) this is extension of the injection from the prime quotient to its fraction
field. Uniqueness is `lem-weil-pbc-prime-residue-field-algebra`, clause (c). -/
theorem spec_field_point_residue_field_map
    (R : Type u) [CommRing R] (K : Type u) [Field K] (ψ : R →+* K) :
    ∃ (q : PrimeSpectrum R)
      (hq : Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint K) = q)
      (l : CommRingCat.of q.asIdeal.ResidueField ⟶ CommRingCat.of K),
      q.asIdeal = RingHom.ker ψ ∧
      l = (Scheme.Spec.residueFieldIso (.of R) q).inv ≫
        ((Spec (.of R)).residueFieldCongr hq).inv ≫
        (Spec (.of R)).descResidueField
          (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ))) ∧
      l.hom.comp (algebraMap R q.asIdeal.ResidueField) = ψ ∧
      ∀ (l' : q.asIdeal.ResidueField →+* K),
        l'.comp (algebraMap R q.asIdeal.ResidueField) = ψ → l' = l.hom := by
  let q := Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint K)
  let l := (Scheme.Spec.residueFieldIso (.of R) q).inv ≫
    (Spec (.of R)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ)))
  have hl : l.hom.comp (algebraMap R q.asIdeal.ResidueField) = ψ := by
    have h := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
      K (Spec (.of R)) (Spec.map (CommRingCat.ofHom ψ))
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField] at h
    rw [← Spec.map_comp_assoc, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  refine ⟨q, rfl, l, ?_, ?_, hl, ?_⟩
  · change Ideal.comap ψ (IsLocalRing.maximalIdeal K) = RingHom.ker ψ
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  · simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv]
    exact (Category.id_comp _).symm
  · intro l' hl'
    exact Ideal.ResidueField.ringHom_ext (hl'.trans hl.symm)

/-- Stacks, Algebra, Local rings and 00CT; Schemes, discussion before 01J9
(blueprint: lem-weil-pbc-spec-field-point-residue-field), final part of clause (3).

Proof: injectivity gives kernel zero, which is the generic point because every prime
contains it (`def-weil-affine-spectrum`). Clause (1) identifies its residue field as a
fraction field of R. Clause (3)'s induced field map extends the given map. It is injective
as a map of fields. Every element of K is a ratio of images of elements of R, with nonzero
denominator; the corresponding ratio in the residue field maps to it. Thus the induced
field map is bijective, hence an isomorphism. -/
theorem spec_field_point_residue_field_generic
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (Spec.map (CommRingCat.ofHom (algebraMap R K)) (IsLocalRing.closedPoint K)).asIdeal = ⊥ ∧
    IsGenericPoint
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) (IsLocalRing.closedPoint K)) Set.univ ∧
    IsIso ((Spec (.of R)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R K))))) := by
  obtain ⟨q, hq, l, hker, hl, hcomp, -⟩ :=
    spec_field_point_residue_field_map R K (algebraMap R K)
  have hqbot : q.asIdeal = ⊥ := by
    rw [hker, ← RingHom.injective_iff_ker_eq_bot]
    exact IsFractionRing.injective R K
  refine ⟨by rw [hq]; exact hqbot, ?_, ?_⟩
  · change closure {_} = Set.univ
    rw [hq, PrimeSpectrum.closure_singleton, hqbot, PrimeSpectrum.zeroLocus_bot]
  · have hsurj : Function.Surjective l.hom := by
      intro z
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective R z
      refine ⟨algebraMap R q.asIdeal.ResidueField a /
        algebraMap R q.asIdeal.ResidueField b, ?_⟩
      rw [map_div₀]
      exact congrArg₂ (· / ·) (RingHom.congr_fun hcomp a) (RingHom.congr_fun hcomp b)
    have : IsIso l := (ConcreteCategory.isIso_iff_bijective l).mpr
      ⟨RingHom.injective l.hom, hsurj⟩
    rw [hl] at this
    rw [isIso_comp_left_iff, isIso_comp_left_iff] at this
    simpa [← hq] using this

end AlgebraicGeometry
