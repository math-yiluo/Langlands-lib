/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Rigidity of pointed maps from a local spectrum to an etale scheme

Source: Stacks Project, Tag 08HQ, uniqueness, and Tag 02GE (open diagonal)
(blueprint: proposition-proper-direct-image-constructible-complexes).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Two maps from a local spectrum to an etale scheme over the same base agree if
some field-valued point over the closed point makes them agree.
Source: Stacks Project, Tag 08HQ, uniqueness, and Tag 02GE (open diagonal)
(blueprint: proposition-proper-direct-image-constructible-complexes).

Proof: The diagonal of the etale morphism is an open immersion. The pair of maps
lifts to its target fibre product. The given point factors through the diagonal,
so the image of the closed point lies in its open range. Every point of a local
spectrum generalizes the closed point. Thus the whole pair map lands in that
range and factors through the diagonal. Its two projections are therefore equal.
Henselianity is unnecessary for this uniqueness argument.
-/
theorem etalePointedMapRigidity
    {B : CommRingCat.{v}} [IsLocalRing B]
    {Ω : Type v} [Field Ω] (β : B →+* Ω) [IsLocalHom β]
    {X S : Scheme.{v}} (f : X ⟶ S) [Etale f]
    (u v : Spec B ⟶ X) (hbase : u ≫ f = v ≫ f)
    (hpoint : Spec.map (CommRingCat.ofHom β) ≫ u =
      Spec.map (CommRingCat.ofHom β) ≫ v) : u = v := by
  let d := pullback.lift u v hbase
  have hd : Spec.map (CommRingCat.ofHom β) ≫ d =
      Spec.map (CommRingCat.ofHom β) ≫ u ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp [d]
    · simpa [d] using hpoint.symm
  have hclosed : d (IsLocalRing.closedPoint B) ∈ Set.range (pullback.diagonal f) := by
    refine ⟨u (IsLocalRing.closedPoint B), ?_⟩
    have hb : Spec.map (CommRingCat.ofHom β) (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint B := IsLocalRing.comap_closedPoint β
    simpa only [Scheme.Hom.comp_apply, hb] using!
      (congrArg (fun q ↦ q (IsLocalRing.closedPoint Ω)) hd).symm
  have hrange : Set.range d ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map d.continuous).mem_open
      (IsOpenImmersion.isOpen_range (pullback.diagonal f)) hclosed
  let l := IsOpenImmersion.lift (pullback.diagonal f) d hrange
  have hl : l ≫ pullback.diagonal f = d :=
    IsOpenImmersion.lift_fac (pullback.diagonal f) d hrange
  have hu := congrArg (fun q ↦ q ≫ pullback.fst f f) hl
  have hv := congrArg (fun q ↦ q ≫ pullback.snd f f) hl
  have hu' : l = u := by simpa [d] using hu
  have hv' : l = v := by simpa [d] using hv
  exact hu'.symm.trans hv' 

end AlgebraicGeometry
