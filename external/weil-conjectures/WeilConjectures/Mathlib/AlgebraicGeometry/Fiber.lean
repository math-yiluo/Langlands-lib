/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Fiber maps of a morphism over a base

A morphism `φ : A ⟶ B` of schemes over `Y` induces, for every morphism `p : P ⟶ Y`, a morphism
`A ×_Y P ⟶ B ×_Y P` between the base changes along `p`. For `p = Y.fromSpecResidueField y` this
is a morphism `a.fiber y ⟶ b.fiber y` between the scheme-theoretic fibers over `y`.

The image of `a.fiber y ⟶ b.fiber y` in `B` is the image under `φ` of the fibre of `a` over
`y`, `AlgebraicGeometry.Scheme.Hom.image_fiberι_range_fiberMap`; in particular one of them is
finite exactly when the other is.

We also record that the fibers of a morphism and of its base change along an open immersion have
the same dimension, `AlgebraicGeometry.topologicalKrullDim_fiber_of_isPullback`.

Finally, the fibres of a morphism locally of finite type are locally connected, so the connected
component of a point in its fibre is open in that fibre,
`AlgebraicGeometry.Scheme.Hom.exists_opens_inter_preimage_subset_connectedComponentIn`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {A B Y P : Scheme.{u}} {a : A ⟶ Y} {b : B ⟶ Y}

/-- The base change `A ×_Y P ⟶ B ×_Y P` along `p : P ⟶ Y` of a morphism `φ : A ⟶ B` over `Y`,
that is, the unique morphism making the diagram

```
  A ×_Y P ── fiberMap φ h p ──▶ B ×_Y P
     │    ╲                  ╱    │
     │     ╲ pullback.snd   ╱     │
     │      ▼              ▼      │
     │             P              │
     │             │ p            │
     ▼             ▼              ▼
     A ───── a ──▶ Y ◀──── b ──── B
      ╲                          ╱
       ╲───────── φ ───────────▶
```

commute. For `p = Y.fromSpecResidueField y` it is a morphism `a.fiber y ⟶ b.fiber y`. -/
noncomputable def fiberMap (φ : A ⟶ B) (h : φ ≫ b = a) (p : P ⟶ Y) :
    pullback a p ⟶ pullback b p :=
  pullback.map a p b p φ (𝟙 P) (𝟙 Y) (by simp [h]) (by simp)

/-- The image in `B` of the fibre map `a.fiber y ⟶ b.fiber y` is the image under `φ` of the fibre
of `a` over `y`. -/
lemma image_fiberι_range_fiberMap (φ : A ⟶ B) (h : φ ≫ b = a) (y : Y) :
    b.fiberι y '' Set.range (fiberMap φ h (Y.fromSpecResidueField y)) = φ '' (a ⁻¹' {y}) := by
  rw [← Set.range_comp, ← a.range_fiberι y, ← Set.range_comp]
  change Set.range (⇑(fiberMap φ h _ ≫ b.fiberι y)) = Set.range (⇑(a.fiberι y ≫ φ))
  congr 2
  simp [fiberMap, fiberι]

/-- The fibre map `a.fiber y ⟶ b.fiber y` has finite image exactly when the image under `φ` of
the fibre of `a` over `y` is finite. -/
lemma finite_range_fiberMap_iff (φ : A ⟶ B) (h : φ ≫ b = a) (y : Y) :
    (Set.range (fiberMap φ h (Y.fromSpecResidueField y))).Finite ↔
      (φ '' (a ⁻¹' {y})).Finite := by
  rw [← image_fiberι_range_fiberMap φ h y,
    Set.finite_image_iff (b.fiberι y).isEmbedding.injective.injOn]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- Base change along an open immersion `g` does not change the fibers: for a pullback square
with `g` an open immersion, the fiber of `snd` at `y` and the fiber of `f` at `g y` have the same
dimension (they are even isomorphic). -/
lemma topologicalKrullDim_fiber_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsOpenImmersion g]
    (y : Y) : topologicalKrullDim (snd.fiber y) = topologicalKrullDim (f.fiber (g y)) := by
  have key {A B C D : Scheme.{u}} {F : A ⟶ B} {G : A ⟶ C} {H : B ⟶ D} {K : C ⟶ D}
      (h : IsPullback F G H K) [IsIso K] : topologicalKrullDim A = topologicalKrullDim B := by
    have := h.isIso_fst_of_isIso
    exact IsHomeomorph.topologicalKrullDim_eq _ F.homeomorph.isHomeomorph
  exact key (isPullback_fiberToSpecResidueField_of_isPullback h y)

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) :
    LocallyConnectedSpace (f.fiber y) :=
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  inferInstance

/-- The fibres of a morphism locally of finite type are locally connected. -/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) :
    LocallyConnectedSpace (f ⁻¹' {y}) :=
  (f.fiberHomeo y).symm.isOpenEmbedding.locallyConnectedSpace

/-- The connected component of a point `x` in the fibre of a morphism `f` locally of finite type
is open in that fibre: some open neighbourhood `U` of `x` meets the fibre inside it. -/
theorem Scheme.Hom.exists_opens_inter_preimage_subset_connectedComponentIn {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      (U : Set X) ∩ f ⁻¹' {f x} ⊆ connectedComponentIn (f ⁻¹' {f x}) x := by
  have hx : x ∈ f ⁻¹' {f x} := rfl
  obtain ⟨t, ht, hct⟩ := isOpen_induced_iff.mp
    (isOpen_connectedComponent (x := (⟨x, hx⟩ : f ⁻¹' {f x})))
  refine ⟨⟨t, ht⟩, ?_, fun y ⟨hyt, hy⟩ ↦ ?_⟩
  · change (⟨x, hx⟩ : f ⁻¹' {f x}) ∈ Subtype.val ⁻¹' t
    rw [hct]
    exact mem_connectedComponent
  · rw [connectedComponentIn_eq_image hx]
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [← hct]
    exact hyt

end AlgebraicGeometry
