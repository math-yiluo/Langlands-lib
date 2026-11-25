/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Spreading a finite étale generic residue field

Source: Stacks Project, Tag 0551, proof (monic polynomial construction).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A specified finite étale generic field extension is the generic residue field
of an étale scheme over the base, compatibly with its given structure map.

Source: Stacks Project, Tag 0551, proof (monic polynomial construction).
Proof: take an affine open through the generic point, with ring R and prime
nilradical p. The extension L of kappa(p) is finite separable. Choose a primitive
element and use `residue_polynomial_lift` to scale it and lift its minimal
polynomial to a monic polynomial over R.
The quotient B is finite free and its fibre over p is the given field L. The unique
prime q over p has residue field L with the prescribed map from kappa(p).
The map Spec B to Spec R is étale at q. Remove the closed image of the complement
of its étale locus and shrink the base to a principal open containing p. The
resulting map is finite étale. For every prime Q of the localized quotient,
flat going down supplies a prime contained in Q over p. Uniqueness forces it to
be q, so q is contained in every Q and is generic. Compose with the affine open
inclusion into S. The residue-field identification gives r; functoriality of
residue-field point morphisms gives
the displayed equality. This construction applies to nonreduced irreducible S
because p is the nilradical, and to the degree-one extension as well.

(blueprint: lem-sbc-etale-generic-residue-field-model) -/
theorem exists_etale_generic_residue_field_model {S : Scheme.{u}}
    [IrreducibleSpace S] {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T)
      (r : Spec (CommRingCat.of (T.residueField η)) ≅ Spec (CommRingCat.of L)),
      Etale g ∧ IsGenericPoint η Set.univ ∧ g η = genericPoint S ∧
      r.hom ≫ yη ≫ S.fromSpecResidueField (genericPoint S) =
        T.fromSpecResidueField η ≫ g := by
  classical
  let : Algebra (S.residueField (genericPoint S)) L := (Spec.preimage yη).hom.toAlgebra
  have hy : Algebra.Etale (S.residueField (genericPoint S)) L := by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    simpa only [Spec.map_preimage] using (inferInstance : Etale yη)
  let : FiniteDimensional (S.residueField (genericPoint S)) L :=
    Algebra.FormallyUnramified.finite_of_free _ _
  let : Algebra.IsSeparable (S.residueField (genericPoint S)) L :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  obtain ⟨U, φ, hφ, u, hu, e, he⟩ :=
    S.exists_etale_neighbourhood_prescribed_residueField (genericPoint S) L
  let : Etale φ := hφ
  obtain ⟨V, hV, hVfiber⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (φ.isDiscrete_preimage_singleton (genericPoint S)) u hu
  have huV : u ∈ V := by
    have : u ∈ V ∩ φ ⁻¹' {genericPoint S} := hVfiber.symm ▸ Set.mem_singleton u
    exact this.1
  let W : U.Opens := ⟨V, hV⟩
  let T := W.toScheme
  let η : T := ⟨u, huV⟩
  let g := W.ι ≫ φ
  have hgη : g η = genericPoint S := hu
  have hfiber : g ⁻¹' {genericPoint S} = {η} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp (hVfiber ▸ ⟨x.property, hx⟩)
    · rintro rfl
      exact hgη
  have hgeneric : IsGenericPoint η Set.univ := by
    rw [IsGenericPoint, ← hfiber,
      ← g.isOpenMap.preimage_closure_eq_closure_preimage g.continuous,
      genericPoint_closure]
    simp
  let d : CommRingCat.of L ≅ T.residueField η :=
    e.toCommRingCatIso ≪≫ asIso (W.ι.residueFieldMap η)
  let r : Spec (CommRingCat.of (T.residueField η)) ≅ Spec (CommRingCat.of L) :=
    Scheme.Spec.mapIso d.op
  have hfields : (S.residueFieldCongr hgη).inv ≫ g.residueFieldMap η =
      Spec.preimage yη ≫ d.hom := by
    ext a
    dsimp [g, d]
    rw [Scheme.residueFieldMap_comp]
    exact congrArg (W.ι.residueFieldMap η).hom (he a).symm
  refine ⟨T, g, η, r, inferInstance, hgeneric, hgη, ?_⟩
  change Spec.map d.hom ≫ yη ≫ S.fromSpecResidueField (genericPoint S) = _
  rw [← Spec.map_preimage yη, ← Spec.map_comp_assoc, ← hfields, Spec.map_comp_assoc,
    Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField]
  exact g.SpecMap_residueFieldMap_fromSpecResidueField η

end AlgebraicGeometry
