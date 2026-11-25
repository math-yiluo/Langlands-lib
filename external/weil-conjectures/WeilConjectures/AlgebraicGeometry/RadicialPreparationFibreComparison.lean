/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.FieldTheory.CommonExtensionFields

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem geometricallyIrreducible_comp_universalHomeomorphism_iff
    {Y Z S : Scheme.{u}} (h : Y ⟶ Z) (p : Z ⟶ S) [IsUniversalHomeomorphism h] :
    GeometricallyIrreducible (h ≫ p) ↔ GeometricallyIrreducible p := by
  simp only [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  constructor <;> intro H K hK z
  · have hi := H K z
    rw [← (pullbackRightPullbackFstIso p z h).hom.homeomorph.irreducibleSpace_iff] at hi
    exact (IsUniversalHomeomorphism.homeomorph
      (pullback.snd h (pullback.fst p z))).irreducibleSpace_iff.mp hi
  · rw [← (pullbackRightPullbackFstIso p z h).hom.homeomorph.irreducibleSpace_iff]
    exact (IsUniversalHomeomorphism.homeomorph
      (pullback.snd h (pullback.fst p z))).irreducibleSpace_iff.mpr (H K z)

private theorem geometricallyIrreducible_field_baseChange_iff
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) :
    GeometricallyIrreducible
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ↔
      GeometricallyIrreducible f := by
  constructor
  · intro h
    refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
    intro K _ _
    obtain ⟨M, _, _, i, j, _, _⟩ := Field.exists_common_extension k k' K
    let g := Spec.map (CommRingCat.ofHom (algebraMap k k'))
    let t := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let a := Spec.map (CommRingCat.ofHom i.toRingHom)
    let b := Spec.map (CommRingCat.ofHom j.toRingHom)
    have hab : a ≫ g = b ≫ t := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (i.commutes x).trans (j.commutes x).symm
    let p := pullback.fst (pullback.snd f t) b
    let q := pullback.snd (pullback.snd f t) b
    let r : pullback (pullback.snd f t) b ⟶ pullback f g :=
      pullback.lift (p ≫ pullback.fst f t) (q ≫ a) (by
        calc
          (p ≫ pullback.fst f t) ≫ f = (p ≫ pullback.snd f t) ≫ t := by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
          _ = (q ≫ b) ≫ t := by
            rw [show p ≫ pullback.snd f t = q ≫ b from pullback.condition]
          _ = (q ≫ a) ≫ g := by simp only [Category.assoc, hab])
    have outer : IsPullback (p ≫ pullback.fst f t) q f (a ≫ g) := by
      rw [hab]
      exact (IsPullback.of_hasPullback (pullback.snd f t) b).flip.paste_vert
        (IsPullback.of_hasPullback f t).flip |>.flip
    have top : IsPullback r q (pullback.snd f g) a := by
      apply IsPullback.flip
      apply IsPullback.of_bot (t := (IsPullback.of_hasPullback f g).flip)
      · simpa [r] using outer.flip
      · simp [r]
    have : IrreducibleSpace ↥(pullback (pullback.snd f t) b) :=
      GeometricallyIrreducible.geometrically_irreducibleSpace (f := pullback.snd f g)
        a r q top
    have : Surjective b := ⟨fun y ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    exact p.surjective.irreducibleSpace p.continuous
  · intro h
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- A universal homeomorphism onto a base-changed family preserves geometric
irreducibility of every fibre.

Source: Stacks Project, Tags 0559 and 0553 (base extension of geometric irreducibility),
and Tag 04DF (universal homeomorphisms).
Proof: for a point s of S, the fibre of the pullback family is the extension of
X_{r(s)} along the residue field map. Geometric irreducibility is unchanged by
this field extension: extend any test field and the new residue field to a common
field, use irreducibility over that common field, and descend along the continuous
surjective projection. The map induced by h on each geometric fibre is a universal
homeomorphism by base-change stability. Its homeomorphism of underlying spaces
preserves irreducibility and nonemptiness. Thus the two geometric irreducibility
tests are equivalent, also when both fibres are empty. No generic-point, finiteness,
reducedness or radicial hypothesis on the base map is needed.

(blueprint: lem-sbc-radicial-preparation-fibre-comparison) -/
theorem exists_radicial_preparation_fibre_comparison
    {X T S Y : Scheme.{u}} (f : X ⟶ T) (r : S ⟶ T)
    (h : Y ⟶ pullback f r) [IsUniversalHomeomorphism h] (s : S) :
    GeometricallyIrreducible ((h ≫ pullback.snd f r).fiberToSpecResidueField s) ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField (r s)) := by
  let p := pullback.snd f r
  let z := S.fromSpecResidueField s
  have hsource :
      GeometricallyIrreducible ((h ≫ p).fiberToSpecResidueField s) ↔
        GeometricallyIrreducible (p.fiberToSpecResidueField s) := by
    change GeometricallyIrreducible (pullback.snd (h ≫ p) z) ↔
      GeometricallyIrreducible (pullback.snd p z)
    let e := pullbackRightPullbackFstIso p z h
    have he : e.hom ≫ pullback.snd (h ≫ p) z =
        pullback.snd h (pullback.fst p z) ≫ pullback.snd p z := by
      simp [e]
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIrreducible) e.hom, he]
    exact geometricallyIrreducible_comp_universalHomeomorphism_iff _ _
  rw [hsource]
  let square := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f r) s
  let e := square.isoPullback
  have he : e.hom ≫ pullback.snd (f.fiberToSpecResidueField (r s))
      (Spec.map (r.residueFieldMap s)) = p.fiberToSpecResidueField s := by
    exact square.isoPullback_hom_snd
  rw [← he]
  have hc := MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyIrreducible) e.hom
    (pullback.snd (f.fiberToSpecResidueField (r s)) (Spec.map (r.residueFieldMap s)))
  rw [hc]
  algebraize [(r.residueFieldMap s).hom]
  exact geometricallyIrreducible_field_baseChange_iff
    (k := T.residueField (r s)) (k' := S.residueField s)
    (f.fiberToSpecResidueField (r s))

end AlgebraicGeometry
