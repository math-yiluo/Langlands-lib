/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.ClosedFibreInteriorComponent
import WeilConjectures.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization
import WeilConjectures.AlgebraicGeometry.NowhereDenseClosedFibreDimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Empty fibre interior for a flat closed family

Source: Stacks Project, Tag 054X, the argument after generic flatness.
(blueprint: lem-sbc-flat-closed-fibre-interior)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Once a family and its closed subfamily are flat and locally finitely presented
on a base open, empty interior in the generic fibre persists on that open.

Source: Stacks Project, Tag 054X, proof after the application of generic flatness;
Tags 03HV and 054U.
Proof: work over U, an integral scheme with generic point eta. If the closed
subfamily has nonempty interior in the fibre at t, this interior contains a
point xi generic in a component of the ambient fibre. In the closed subfamily
it is also generic in a fibre component. Flatness of the closed subfamily
lifts the generalization eta of t to a generalization xi' of xi over eta,
by Tag 03HV. The dimensions at xi of the closed and ambient fibres agree,
since a neighbourhood of xi in the ambient fibre is contained in the closed
subfamily. Tag 054U, applied to the two flat locally finitely presented maps,
identifies each of these dimensions with its value at xi' in the corresponding
generic fibre. A component of the closed generic fibre through xi' therefore
has dimension equal to the ambient local fibre dimension there. Since the
ambient generic fibre is of finite type over a field, a proper closed subset
of every irreducible component has strictly smaller dimension. Thus some
ambient component is contained in the closed generic fibre, contradicting
its empty interior. This proves the assertion. Empty fibres have empty
interior and require no choice of xi. The open U may equal the whole base;
the assertion uses no reducedness of the source or of the closed subfamily.

(blueprint: lem-sbc-flat-closed-fibre-interior) -/
theorem interior_fibre_closed_eq_empty_of_flat_restrict
    {Z X T : Scheme.{u}} [IsIntegral T]
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (η : T) (hη : IsGenericPoint η Set.univ)
    (U : T.Opens) (hηU : η ∈ U)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    [Flat ((i ≫ f) ∣_ U)] [LocallyOfFinitePresentation ((i ≫ f) ∣_ U)]
    (hgeneric : interior ((f.fiberι η) ⁻¹' Set.range i) = ∅) :
    ∀ t ∈ U, interior ((f.fiberι t) ⁻¹' Set.range i) = ∅ := by
  intro t ht
  by_contra hne
  have hnonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hdense : Dense (genericPoints (f.fiber t)) := by
    rw [dense_iff_closure_eq]
    exact genericPoints.closure
  obtain ⟨ξ, hξcomp, hξinterior⟩ := hdense.exists_mem_open isOpen_interior hnonempty
  obtain ⟨z, hiz⟩ := interior_subset hξinterior
  have hft : f (f.fiberι t ξ) = t := by
    have hrange := Set.mem_range_self ξ (f := f.fiberι t)
    rw [f.range_fiberι] at hrange
    exact hrange
  have hzt : (i ≫ f) z = t := by
    rw [Scheme.Hom.comp_apply, hiz, hft]
  have hfit : f (i z) = t := by rw [hiz, hft]
  subst t
  have hξ : f.asFiber (i z) = ξ := by
    apply (f.fiberι (f (i z))).isEmbedding.injective
    simpa using hiz
  have hxcomp : f.asFiber (i z) ∈ genericPoints (f.fiber (f (i z))) := hξ ▸ hξcomp
  have hxinterior : f.asFiber (i z) ∈
      interior ((f.fiberι (f (i z))) ⁻¹' Set.range i) := hξ ▸ hξinterior
  obtain ⟨hzcomp, hdim⟩ :=
    common_fibre_component_dimension_of_mem_interior f i z hxinterior hxcomp
  let g := i ≫ f
  let zU : (g ⁻¹ᵁ U).toScheme := ⟨z, by exact ht⟩
  let ηU : U.toScheme := ⟨η, hηU⟩
  have hspU : ηU ⤳ (g ∣_ U) zU := by
    apply U.ι.isEmbedding.isInducing.specializes_iff.mp
    exact hη.specializes (Set.mem_univ _)
  obtain ⟨zU', hzz, hη'⟩ := Flat.generalizingMap (g ∣_ U) hspU
  let z' : Z := (g ⁻¹ᵁ U).ι zU'
  have hsp : z' ⤳ z := hzz.map (g ⁻¹ᵁ U).ι.continuous
  have hz' : g z' = η := by
    have := congrArg (fun y : U.toScheme ↦ U.ι y) hη'
    simpa [z', ηU] using this
  have hzU : g z ∈ U := by exact ht
  have hZdim := fibre_dimension_eq_of_specializes_component_restrict
    g U z z' hzU hsp hzcomp
  have hxU : f (i z) ∈ U := by simpa [g, Scheme.Hom.comp_apply] using hzU
  have hXdim := fibre_dimension_eq_of_specializes_component_restrict
    f U (i z) (i z') hxU (hsp.map i.continuous) hxcomp
  have hlt := fibre_dimension_lt_of_closed_interior_eq_empty f i η hgeneric z' hz'
  have heq : topologicalKrullDimAt (g.asFiber z') =
      topologicalKrullDimAt (f.asFiber (i z')) := hZdim.trans (hdim.trans hXdim.symm)
  exact (ne_of_lt hlt) heq


end AlgebraicGeometry
