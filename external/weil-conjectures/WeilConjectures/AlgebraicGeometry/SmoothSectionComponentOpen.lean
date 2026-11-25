/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import WeilConjectures.AlgebraicGeometry.SectionComponentLocallyConstructible
import WeilConjectures.AlgebraicGeometry.SmoothSectionComponentGeneralization

/-!
# Openness of the fibre components meeting a smooth section

Source: Stacks Project, Tags 055R and 055Q.
(blueprint: lem-sbc-smooth-section-component-open)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a smooth, quasi-compact, quasi-separated morphism with a section, the union of
fibre connected components meeting the section is open (Stacks 055R, using 055Q).

Proof: smoothness gives flatness and geometrically reduced fibres; quasi-compactness and
quasi-separatedness give finite presentation. Work locally on the base. Descend the finitely
presented morphism and its section to a noetherian base, retaining flatness. The component
locus commutes with base change since its component contains a rational point. On the
noetherian model, test neighbourhoods along irreducible closed subsets through a point of
the locus. A discrete valuation ring joining the special point to the generic point reduces
this test to a flat family over a trait with geometrically reduced special fibre. Remove
the other special-fibre components and retain the total-space component containing the
section. Connectedness of the special fibre then implies connectedness of the generic fibre
(Stacks 055Q). Thus the generic point belongs to the locus, proving the neighbourhood
criterion. Every point of the locus has such a neighbourhood, so the locus is open.

(blueprint: lem-sbc-smooth-section-component-open) -/
theorem Smooth.isOpen_section_component {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    IsOpen {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  let S : Set P := {p | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))}
  have hcons : Topology.IsLocallyConstructible S :=
    isLocallyConstructible_section_component g σ hσ
  have hgen : StableUnderGeneralization S :=
    Smooth.stableUnderGeneralization_section_component g σ hσ
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨q, hq⟩ := P.affineCover.covers p
  let j := P.affineCover.f (P.affineCover.idx p)
  have hpre : IsOpen (j ⁻¹' S) := by
    exact PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
      (hgen.preimage j.continuous)
      ((hcons.preimage_of_isOpenEmbedding j.isOpenEmbedding).isConstructible)
  have hopen : IsOpen (j '' (j ⁻¹' S)) := j.isOpenEmbedding.isOpenMap _ hpre
  have hmem : p ∈ j '' (j ⁻¹' S) := by
    refine ⟨q, ?_, hq⟩
    change j q ∈ S
    rw [show j q = p from hq]
    exact hp
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) (Set.image_preimage_subset j S)

end AlgebraicGeometry
