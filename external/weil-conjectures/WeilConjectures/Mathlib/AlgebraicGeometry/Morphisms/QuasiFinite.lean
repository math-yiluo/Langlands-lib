/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension under quasi-finite morphisms

## Main statements

- `AlgebraicGeometry.LocallyQuasiFinite.of_etale`: an étale morphism is locally quasi-finite.
- `AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified`: a formally unramified morphism
  locally of finite type is locally quasi-finite.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_surjective`: a universally closed,
  locally quasi-finite, surjective morphism of schemes (for instance a finite surjective one)
  preserves the dimension.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton_of_isFinite_morphismRestrict`: a
  morphism that is finite over an open `U` has finite fibres over the points of `U`.
- `AlgebraicGeometry.LocallyQuasiFinite.of_isPullback_of_surjective`: local quasi-finiteness of
  a quasi-compact morphism locally of finite type descends along surjective base changes.
- `AlgebraicGeometry.Scheme.Hom.coheight_apply_of_flat`: a flat, locally quasi-finite morphism
  preserves the codimension of points.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le_of_locallyQuasiFinite`: a locally
  quasi-finite morphism, for instance an étale one, does not increase dimension.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- An étale morphism is locally quasi-finite. -/
instance (priority := low) LocallyQuasiFinite.of_etale (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have := HasRingHomProperty.appLE (P := @Etale) f ‹_› U V e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- A formally unramified morphism locally of finite type is locally quasi-finite: on affine
opens, a formally unramified algebra of finite type is quasi-finite. -/
instance (priority := low) LocallyQuasiFinite.of_formallyUnramified (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h₁ := f.formallyUnramified_appLE U.2 V.2 e
  have h₂ := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› U V e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- A locally quasi-finite morphism identifies no two distinct points `x ⤳ x'`: its fibres are
discrete. -/
lemma Scheme.Hom.eq_of_specializes_of_apply_eq (f : X ⟶ Y) [LocallyQuasiFinite f] {x x' : X}
    (h : x ⤳ x') (hx : f x = f x') : x = x' := by
  have : DiscreteTopology (f ⁻¹' {f x'}) := (f.isDiscrete_preimage_singleton (f x')).to_subtype
  have h' : (⟨x, hx⟩ : f ⁻¹' {f x'}) ⤳ ⟨x', rfl⟩ := IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

/-- **A universally closed, locally quasi-finite, surjective morphism preserves the dimension.**
Such a morphism `f : X ⟶ Y`, for instance a finite surjective one, satisfies `dim X = dim Y`:
chains of specializations in `Y` lift to `X` since `f` is closed (going up), and their images in
`Y` stay strict since the fibres of `f` are discrete (incomparability). -/
theorem Scheme.Hom.topologicalKrullDim_eq_of_surjective (f : X ⟶ Y) [UniversallyClosed f]
    [LocallyQuasiFinite f] [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm
    (topologicalKrullDim_le_of_continuous f.continuous fun _ _ ↦ f.eq_of_specializes_of_apply_eq)
    (topologicalKrullDim_le_of_specializingMap f.isClosedMap.specializingMap f.surjective)

/-- If the restriction of `f` over an open `U` is finite, then the fibre of `f` over any point
of `U` is finite. -/
lemma Scheme.Hom.finite_preimage_singleton_of_isFinite_morphismRestrict (f : X ⟶ Y)
    {U : Y.Opens} [IsFinite (f ∣_ U)] {y : Y} (hy : y ∈ U) : (f ⁻¹' {y}).Finite := by
  refine (((f ∣_ U).finite_preimage_singleton ⟨y, hy⟩).image (f ⁻¹ᵁ U).ι).subset ?_
  intro x hx
  refine ⟨⟨x, by simp_all⟩, Subtype.ext ?_, rfl⟩
  simpa [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base] using hx

/-- **Quasi-finiteness descends along surjective base changes.** Let `f : X ⟶ Z` be quasi-compact
and locally of finite type, and let `snd : P ⟶ Y` be its base change along a surjective
`g : Y ⟶ Z`. If `snd` is locally quasi-finite, so is `f`: every fibre of `f` is the image of a
fibre of `snd`, which is finite. The hypothesis `QuasiCompact f` is only a convenience, used to
get finite fibres of `snd`; the statement also holds without it. -/
lemma LocallyQuasiFinite.of_isPullback_of_surjective {P Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Surjective g]
    [LocallyQuasiFinite snd] [QuasiCompact f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  have : QuasiCompact snd := MorphismProperty.of_isPullback h ‹_›
  refine .of_finite_preimage_singleton f fun z ↦ ?_
  obtain ⟨y, rfl⟩ := g.surjective z
  refine ((snd.finite_preimage_singleton y).image fst).subset fun x hx ↦ ?_
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hx
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, hw₂]
  · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, hw₁]

open Order in
/-- **Flat locally quasi-finite morphisms preserve codimension.** For a flat, locally
quasi-finite morphism `f`, the codimension (coheight in the specialisation order) of `f y` is that
of `y`: chains of generisations of `y` map to chains of generisations of `f y`, as no two points
of a fibre specialise to each other, and chains of generisations of `f y` lift, as flat morphisms
are generalizing. -/
lemma Scheme.Hom.coheight_apply_of_flat (f : X ⟶ Y) [Flat f] [LocallyQuasiFinite f] (y : X) :
    coheight (f y) = coheight y := by
  have hf : StrictMono f := by
    intro a b hab
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
    refine ⟨hab.1.map f.continuous, fun h ↦ hab.2 ?_⟩
    have := f.eq_of_specializes_of_apply_eq hab.1 (h.antisymm (hab.1.map f.continuous)).eq.symm
    rw [this]
  refine (coheight_eq_of_strictMono f hf (fun a b hab ↦ ?_) y).symm
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab
  obtain ⟨a', ha', rfl⟩ := Flat.generalizingMap f hab.1
  refine ⟨a', ?_, rfl⟩
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact ⟨ha', fun h ↦ hab.2 (h.map f.continuous)⟩

/-- **A locally quasi-finite morphism does not increase dimension.** For `f : X ⟶ Y` locally
quasi-finite, `dim X ≤ dim Y`: the fibres of `f` are discrete, so `f` maps strict chains of
specializations to strict chains.

Used for blueprint `theorem-results-from-etale-theory--4`: an étale `X`-scheme has dimension at
most `dim X`. -/
theorem Scheme.Hom.topologicalKrullDim_le_of_locallyQuasiFinite (f : X ⟶ Y)
    [LocallyQuasiFinite f] : topologicalKrullDim X ≤ topologicalKrullDim Y :=
  topologicalKrullDim_le_of_continuous f.continuous fun _ _ ↦ f.eq_of_specializes_of_apply_eq

/-- **An étale morphism does not increase dimension.** For `f : X ⟶ Y` étale, `dim X ≤ dim Y`.

Used for blueprint `theorem-results-from-etale-theory--4`: an étale `X`-scheme has dimension at
most `dim X`. -/
theorem Scheme.Hom.topologicalKrullDim_le_of_etale (f : X ⟶ Y) [Etale f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  f.topologicalKrullDim_le_of_locallyQuasiFinite

end AlgebraicGeometry
