/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.GenericFibreAffineOpenLift
import WeilConjectures.AlgebraicGeometry.GenericFibreIsoSpreadBaseOpen

/-! # Spreading a partial isomorphism of generic fibres to a common open

Source: Stacks Project, Tag 0559, first proof, the common-open paragraph;
Tag 0552, the finite-generator common-localization argument;
Tag 01ZM, morphism descent and eventual equality.
(blueprint: lem-sbc-generic-fibre-partial-iso-spread-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A partial isomorphism of nonempty generic fibres of finitely presented affine
families spreads to a common open over the original integral affine base.

Source: Stacks Project, Tag 0559, first proof, the common-open paragraph; Tag 0552;
Tag 01ZM, morphism descent and eventual equality.
Proof: Density and nonemptiness give a point in the source of the partial
isomorphism. Choose an affine neighbourhood A inside that source. Its images
U and T under the source inclusion and the partial isomorphism followed by
the target inclusion are affine, since both maps are open immersions. The
canonical image isomorphisms identify U and T over the generic residue field.
Lift U and T to affine opens V of X and W of Y, with compatible generic-fibre
isomorphisms, using exists_affine_open_lift_of_generic_fibre. Transport the
isomorphism U -> T to V_eta -> W_eta. The opens V and W are still locally
finitely presented over S. Apply exists_base_open_iso_of_generic_fibre_iso
to descend this isomorphism to their restrictions above a base neighbourhood
B of eta. The preimage Z of B in V has an open image O in X. Compose the
canonical image isomorphism O -> Z with the descended isomorphism and the
target open inclusions to obtain an open immersion i:O -> Y over S. Transport
the original point of U to V_eta; its fibre-inclusion image maps to eta,
and therefore belongs to Z since eta lies in B. Its image in O proves eta
lies in the range of O -> S. This argument allows arbitrary vertical
components and nilpotents in the special fibres.

(blueprint: lem-sbc-generic-fibre-partial-iso-spread-open) -/
theorem exists_open_of_generic_fibre_partial_iso
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) (g : Y ⟶ S)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ) [Nonempty (f.fiber η)]
    (p : (f.fiber η).PartialIso (g.fiber η))
    (hp : p.IsOver (f.fiberToSpecResidueField η) (g.fiberToSpecResidueField η)) :
    ∃ V : X.Opens, η ∈ Set.range (V.ι ≫ f) ∧
      ∃ i : V.toScheme ⟶ Y, IsOpenImmersion i ∧ i ≫ g = V.ι ≫ f := by
  obtain ⟨x, hx⟩ := p.dense_source.nonempty
  obtain ⟨A, hA, hxA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := p.source.toScheme) (x := ⟨x, hx⟩) (U := ⊤) (by trivial)
  let U := p.source.ι ''ᵁ A
  let j := p.iso.hom ≫ p.target.ι
  let T := j ''ᵁ A
  have hU : IsAffineOpen U := hA.image_of_isOpenImmersion p.source.ι
  have hT : IsAffineOpen T := hA.image_of_isOpenImmersion j
  let e : U.toScheme ≅ T.toScheme :=
    (p.source.ι.isoImage A).symm ≪≫ j.isoImage A
  have he : e.hom ≫ T.ι ≫ g.fiberToSpecResidueField η =
      U.ι ≫ f.fiberToSpecResidueField η := by
    dsimp [e, T, j, U]
    simp only [Category.assoc, Scheme.Hom.isoImage_hom_ι_assoc]
    rw [hp]
    exact Scheme.Hom.isoImage_inv_ι_assoc _ _ _
  obtain ⟨V, hV, a, _, ha⟩ := exists_affine_open_lift_of_generic_fibre f η hη U hU
  obtain ⟨W, hW, b, _, hb⟩ := exists_affine_open_lift_of_generic_fibre g η hη T hT
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  let e' : (V.ι ≫ f).fiber η ≅ (W.ι ≫ g).fiber η := a ≪≫ e ≪≫ b.symm
  have he' : e'.hom ≫ (W.ι ≫ g).fiberToSpecResidueField η =
      (V.ι ≫ f).fiberToSpecResidueField η := by
    change (a.hom ≫ e.hom ≫ b.inv) ≫ _ = _
    simp only [Category.assoc]
    rw [← hb]
    simp only [Iso.inv_hom_id_assoc]
    rw [he, ha]
  obtain ⟨B, hηB, c, hc⟩ :=
    exists_base_open_iso_of_generic_fibre_iso (V.ι ≫ f) (W.ι ≫ g) η hη e' he'
  let Z := (V.ι ≫ f) ⁻¹ᵁ B
  let Z' := (W.ι ≫ g) ⁻¹ᵁ B
  let O := V.ι ''ᵁ Z
  let i : O.toScheme ⟶ Y :=
    (V.ι.isoImage Z).inv ≫ c.hom ≫ Z'.ι ≫ W.ι
  refine ⟨O, ?_, i, inferInstance, ?_⟩
  · have hxU : x ∈ U := ⟨⟨x, hx⟩, hxA, rfl⟩
    let z := a.inv ⟨x, hxU⟩
    let v := (V.ι ≫ f).fiberι η z
    have hv : (V.ι ≫ f) v = η := by
      have hv' : v ∈ Set.range ((V.ι ≫ f).fiberι η) := ⟨z, rfl⟩
      rw [Scheme.Hom.range_fiberι] at hv'
      exact hv'
    have hvZ : v ∈ Z := by
      change (V.ι ≫ f) v ∈ B
      rwa [hv]
    refine ⟨⟨V.ι v, ⟨v, hvZ, rfl⟩⟩, ?_⟩
    change f (V.ι v) = η
    exact hv
  · dsimp [i]
    simp only [Category.assoc]
    have hc' : c.hom ≫ Z'.ι ≫ W.ι ≫ g = Z.ι ≫ V.ι ≫ f := hc
    rw [hc']
    exact Scheme.Hom.isoImage_inv_ι_assoc _ _ _

end AlgebraicGeometry
