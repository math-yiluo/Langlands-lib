/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import all WeilConjectures.AlgebraicGeometry.SectionRingProjPreimageForward

/-! # Free generation on a second section-ring chart

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
(blueprint: lem-sc-section-ring-second-chart-generator).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem generatesAt_of_unit_smul {X : Scheme.{v}} (M : X.Modules)
    (a b : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U))
    (h : r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op b)
    (x : X) (hx : x ∈ X.basicOpen r) (ha : GeneratesAt a x) : GeneratesAt b x := by
  obtain ⟨V, hxV, hV⟩ := ha
  let W := V ⊓ X.basicOpen r
  have hWU : W ≤ U := inf_le_right.trans (X.basicOpen_le r)
  have hu : IsUnit (X.presheaf.map (homOfLE hWU).op r) := by
    have hu := X.toRingedSpace.isUnit_res_basicOpen r
    have hu' := hu.map (X.presheaf.map (homOfLE (show W ≤ X.basicOpen r from
      inf_le_right)).op).hom
    change IsUnit (X.presheaf.map (homOfLE (show W ≤ X.basicOpen r from
      inf_le_right)).op (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r)) at hu'
    simpa only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp] using hu'
  refine ⟨W, ⟨hxV, hx⟩, ?_⟩
  have hb := congrArg (M.presheaf.map (homOfLE hWU).op) h
  rw [map_smul, presheaf_map_homOfLE_map_homOfLE,
    presheaf_map_homOfLE_map_homOfLE] at hb
  rw [← hb, ← hu.unit_spec]
  have haW := hV.map (show W ≤ V from inf_le_left)
  rw [presheaf_map_homOfLE_map_homOfLE] at haW
  exact haW.units_smul hu.unit

/-- The second section freely generates its tensor power on its chart preimage.
Source: Stacks Project, Constructions, Tag 01N8, comparison of chart preimages;
Tag 01NK, comparison of different positive degrees.
(blueprint: lem-sc-section-ring-second-chart-generator).

Proof: On a local trivialization z of L in U, write s=b z^d and t=c z^e.
The hypothesis on s says b is invertible. Apply hρ with exponent e and
numerator t^d (transporting d*e=e*d) to identify ρ(t^d/s^e) with c^d/b^e.
The inverse image of D_+(t) in the s-chart is the principal open of t^d/s^e;
use the affine basic-open preimage formula and hq to identify its inverse
image in U with the unit locus of c^d/b^e. This is the unit locus of c,
since b is invertible and d>0. Thus t is a unit multiple of z^e there.
Its multiplication map is an isomorphism on each such local trivialization.
These isomorphisms agree, because each is multiplication by the same section t,
and glue to a trivialization on the ambient image W. This also proves the
bijectivity on every subopen required by IsFreeGenerator. Empty W causes no
exception: all its modules of sections have one element. No reducedness is used. -/
theorem sectionRing_second_chart_generator
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d)))
    (ρ : HomogeneousLocalization.Away (sectionRingGrade L) s.val →+* Γ(X, U))
    (hρ : ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      ρ (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property) •
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((s.val ^ n) (n • d)) =
      (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (ξ.val (n • d)))
    (q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      (sectionRingGrade L) s.val)))
    (hq : (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
        (sectionRingGrade L) s.val))).inv ≫ q.appTop =
      CommRingCat.ofHom ρ ≫ U.topIso.inv) :
    let g := q ≫ Proj.awayι (sectionRingGrade L) s.val s.property hd
    ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e),
      IsFreeGenerator ((L.tensorPow e).presheaf.map (homOfLE
        (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤ ⊤)).op
        (t.val e)) := by
  dsimp only
  intro e he t
  let r := HomogeneousLocalization.Away.isLocalizationElem s.property t.property
  have hW : U.ι ''ᵁ ((q ≫ Proj.awayι (sectionRingGrade L) s.val s.property hd) ⁻¹ᵁ
      Proj.basicOpen (sectionRingGrade L) t.val) = X.basicOpen (ρ r) := by
    rw [Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen
      (sectionRingGrade L) s.property hd t.property he]
    rw [← basicOpen_eq_of_affine
      (R := .of (HomogeneousLocalization.Away (sectionRingGrade L) s.val)) r,
      Scheme.preimage_basicOpen_top]
    have happ : q.appTop ((Scheme.ΓSpecIso _).inv r) = U.topIso.inv (ρ r) := by
      exact congrArg (fun f ↦ f r) hq
    rw [happ, U.ι_image_basicOpen_topIso_inv]
  rw [hW]
  have hle : X.basicOpen (ρ r) ≤ generatingLocus (t.val e) := by
    intro x hx
    have hxU := X.basicOpen_le (ρ r) hx
    have hsx : x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) :=
      (mem_nonvanishingLocus_iff_generatesAt _ _ _).mpr ⟨U, hxU, hs⟩
    have hsp := (nonvanishing_power L s e he x).mpr hsx
    have hdeg : d • e = e • d := Nat.mul_comm d e
    let ξ : sectionRingGrade L (e • d) :=
      ⟨t.val ^ d, hdeg ▸ SetLike.pow_mem_graded d t.property⟩
    have hr : HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property e
        ξ.val ξ.property = r := rfl
    have hformula := hρ e ξ
    rw [hr] at hformula
    have ht := generatesAt_of_unit_smul (L.tensorPow (e • d))
      ((s.val ^ e) (e • d)) (ξ.val (e • d)) U (ρ r) hformula x hx
      ((mem_nonvanishingLocus_iff_generatesAt _ _ _).mp hsp)
    have htp : x ∈ nonvanishingLocus (L.tensorPow (d • e))
        ((t.val ^ d) (d • e)) := by
      rw [hdeg]
      exact (mem_nonvanishingLocus_iff_generatesAt _ _ _).mpr ht
    exact (mem_nonvanishingLocus_iff_generatesAt _ _ _).mp
      ((nonvanishing_power L t d hd x).mp htp)
  have ht := (isFreeGenerator_generatingLocus (t.val e)).map hle
  simpa only [presheaf_map_homOfLE_map_homOfLE] using ht

end AlgebraicGeometry.Scheme.Modules
