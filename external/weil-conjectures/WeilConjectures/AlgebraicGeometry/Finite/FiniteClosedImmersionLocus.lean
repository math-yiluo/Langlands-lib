/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteClosedImmersionNearFibre
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# The closed-immersion locus of a finite morphism

Source: Stacks Project, Tags 04DG and 056J, applied to the marked-open step of 0GK7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem closedImmersion_fiber_descend
    {Y X Y₀ X₀ : Scheme.{u}} {f : Y ⟶ X} {f₀ : Y₀ ⟶ X₀}
    {b : Y₀ ⟶ Y} {a : X₀ ⟶ X} (H : IsPullback b f₀ f a) (x : X₀)
    (h : IsClosedImmersion (f₀.fiberToSpecResidueField x)) :
    IsClosedImmersion (f.fiberToSpecResidueField (a x)) := by
  let : Algebra (X.residueField (a x)) (X₀.residueField x) :=
    (a.residueFieldMap x).hom.toAlgebra
  have := IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact.{u}
  have hflat := (flat_and_surjective_SpecMap_iff (a.residueFieldMap x)).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsClosedImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_fiberToSpecResidueField_of_isPullback H x).flip
    ⟨⟨hflat.2, hflat.1⟩, inferInstance⟩ h

/-- A finite morphism is a closed immersion over an open containing every open
closed-immersion locus of an arbitrary base change.

Source: Stacks Project, Morphisms, Tags 04DG and 056J; the marked-open paragraph of
Tag 0GK7. (blueprint: lem-weil-pbc-finite-closed-immersion-locus)

Proof: A closed-immersion fibre spreads to a neighbourhood by the finite-cokernel
and Nakayama argument of 04DG. The set of such fibres is consequently open: every
point of that neighbourhood has a closed-immersion fibre, using the restriction
square and descent along the extension of residue fields. Let W be this set.
The restriction to W has closed-immersion fibres, hence is locally on its target
a closed immersion by the same neighbourhood theorem, and these local assertions
glue. For x in W₀, the closed immersion over W₀ has a closed-immersion fibre.
Descend this first through W₀ → X₀ and then through the given cartesian square.
Descent here is only along field extensions, which are faithfully flat; the
original base change a is arbitrary. Empty opens and empty fibres cause no exception.
-/
theorem exists_finite_closedImmersion_locus
    {Y X Y₀ X₀ : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (f₀ : Y₀ ⟶ X₀) (b : Y₀ ⟶ Y) (a : X₀ ⟶ X)
    (H : IsPullback b f₀ f a) (W₀ : X₀.Opens)
    (hW₀ : IsClosedImmersion (pullback.snd f₀ W₀.ι)) :
    ∃ W : X.Opens, IsClosedImmersion (pullback.snd f W.ι) ∧ W₀ ≤ a ⁻¹ᵁ W := by
  have hopen : IsOpen {x : X | IsClosedImmersion (f.fiberToSpecResidueField x)} := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hxU, hU⟩ := exists_isClosedImmersion_restrict_of_fiber f x hx
    refine ⟨U, ?_, U.isOpen, hxU⟩
    intro y hy
    have : IsClosedImmersion (f ∣_ U) := hU
    exact closedImmersion_fiber_descend (isPullback_morphismRestrict f U).flip
      ⟨y, hy⟩ (by
        dsimp only [Scheme.Hom.fiberToSpecResidueField]
        infer_instance)
  let W : X.Opens := ⟨_, hopen⟩
  have hrestrict : IsClosedImmersion (f ∣_ W) := by
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    intro x
    have hpb := isPullback_fiberToSpecResidueField_of_isPullback
      (isPullback_morphismRestrict f W).flip x
    have hfiber : IsClosedImmersion ((f ∣_ W).fiberToSpecResidueField x) :=
      MorphismProperty.of_isPullback hpb x.property
    exact exists_isClosedImmersion_restrict_of_fiber (f ∣_ W) x hfiber
  refine ⟨W, ?_, ?_⟩
  · have e := morphismRestrictOpensRange f W.ι
    rw [Scheme.Opens.opensRange_ι] at e
    exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).mp hrestrict
  · intro x hx
    have : IsClosedImmersion (pullback.snd f₀ W₀.ι) := hW₀
    have hfiber : IsClosedImmersion (f₀.fiberToSpecResidueField x) := by
      exact closedImmersion_fiber_descend (.of_hasPullback f₀ W₀.ι) ⟨x, hx⟩
        (by
          dsimp only [Scheme.Hom.fiberToSpecResidueField]
          infer_instance)
    exact closedImmersion_fiber_descend H x hfiber

end AlgebraicGeometry
