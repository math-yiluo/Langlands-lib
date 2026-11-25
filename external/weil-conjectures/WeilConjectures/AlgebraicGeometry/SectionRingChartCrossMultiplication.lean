/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.ProjChartPullbackFractionRelation

/-! # Clearing denominators between section-ring charts

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
(blueprint: lem-sc-section-ring-chart-cross-multiplication).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The numerator identity after clearing the second-chart denominator.
Source: Stacks Project, Constructions, Tag 01N8, comparison on overlapping charts;
Tag 01NK, passage between different positive degrees.
(blueprint: lem-sc-section-ring-chart-cross-multiplication).

Proof: Put k=n*(d-1), i=n*e and j=k*e. Then i+j=n*e*d.
On the chart intersection let r=t^d/s^e and η=ξ*t^k, so η has degree n*e*d.
The homogeneous-localization identity (ξ/t^n)*r^n=η/s^(n*e) follows by
multiplying numerators and denominators: n+k=n*d. Restrict this identity to
the intersection and pull it back along q. The chart restriction on the
s-side is localization at r; its map on sections agrees with ρ by hq.
Use hρ with exponent n*e and numerator η, and with exponent e and numerator t^d.
Locally write s=b*z^d and t=c*z^e in a basis z of L, where b is a unit.
The pulled-back identity becomes a*(c^d/b^e)^n=η_coeff/b^(n*e), where a is
exactly the displayed pullback of ξ/t^n. Multiply by the unit b^(n*e):
a*c^(n*d)=η_coeff. Tensor multiplication identifies c^(n*d)*z^(n*e*d)
with the displayed tensor of t^n and t^k through tensorPowAddIso.
Thus the cleared identity holds locally. Naturality of tensor sections and
of tensorPowAddIso lets these equalities glue on the ambient image W.
This argument does not cancel c or assume t generates on W. For n=0 the
identity has no denominators or extra factors, and for d=1 one has k=0.
Empty intersections have unique sections, so the same conclusion holds there. -/
theorem sectionRing_chart_cross_multiplication
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
    ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
        (n : ℕ) (ξ : sectionRingGrade L (n • e)),
      let W := U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val)
      let k := n * (d - 1)
      (show Γ(X, W) from
        g.app (Proj.basicOpen (sectionRingGrade L) t.val)
          (Proj.awayToSection (sectionRingGrade L) t.val
            (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
              ξ.val ξ.property))) •
        (L.tensorPowAddIso (n • e) (k • e)).inv.app W
          (tmulSection
            ((L.tensorPow (n • e)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
              ((t.val ^ n) (n • e)))
            ((L.tensorPow (k • e)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
              ((t.val ^ k) (k • e)))) =
        (L.tensorPow (n • e + k • e)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          ((ξ.val * t.val ^ k) (n • e + k • e)) := by
  have _ := hs
  dsimp only
  intro e he t n ξ
  clear he
  let g := q ≫ Proj.awayι (sectionRingGrade L) s.val s.property hd
  let W := U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val)
  let k := n * (d - 1)
  have hdeg : n • e + k • e = (n * e) • d := by
    dsimp [k]
    have hd' : d - 1 + 1 = d := Nat.sub_add_cancel hd
    conv_rhs => rw [← hd']
    ring
  let p₀ : sectionRingGrade L (n • e + k • e) :=
    ⟨t.val ^ n * t.val ^ k,
      SetLike.mul_mem_graded (SetLike.pow_mem_graded n t.property)
        (SetLike.pow_mem_graded k t.property)⟩
  let r₀ : sectionRingGrade L (n • e + k • e) :=
    ⟨ξ.val * t.val ^ k,
      SetLike.mul_mem_graded ξ.property (SetLike.pow_mem_graded k t.property)⟩
  let p : sectionRingGrade L ((n * e) • d) := ⟨p₀.val, hdeg ▸ p₀.property⟩
  let r : sectionRingGrade L ((n * e) • d) := ⟨r₀.val, hdeg ▸ r₀.property⟩
  have hmul : ξ.val * p.val = r.val * t.val ^ n := by
    dsimp [p, r, p₀, r₀]
    ring
  have hc := Proj.chart_pullback_fraction_relation (InvertibleSectionRing L)
    (sectionRingGrade L) X d s hd U ρ q hq e t n (n * e) ξ p r hmul
  dsimp only at hc
  have hp := congrArg ((L.tensorPow ((n * e) • d)).presheaf.map
    (homOfLE (U.ι_image_le (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val))).op)
    (hρ (n * e) p)
  have hr := congrArg ((L.tensorPow ((n * e) • d)).presheaf.map
    (homOfLE (U.ι_image_le (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val))).op)
    (hρ (n * e) r)
  simp only [map_smul, presheaf_map_homOfLE_map_homOfLE] at hp hr
  have hpr :
      (show Γ(X, W) from g.app (Proj.basicOpen (sectionRingGrade L) t.val)
        (Proj.awayToSection (sectionRingGrade L) t.val
          (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
            ξ.val ξ.property))) •
        (L.tensorPow ((n * e) • d)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          (p.val ((n * e) • d)) =
      (L.tensorPow ((n * e) • d)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (r.val ((n * e) • d)) := by
    rw [← hp, smul_smul, hc, hr]
  have hm : (t.val ^ n * t.val ^ k) (n • e + k • e) =
      (L.tensorPowAddIso (n • e) (k • e)).inv.app ⊤
        (tmulSection ((t.val ^ n) (n • e)) ((t.val ^ k) (k • e))) := by
    obtain ⟨tn, htn⟩ := (show sectionRingGrade L (n • e) from
      ⟨t.val ^ n, SetLike.pow_mem_graded n t.property⟩).property
    obtain ⟨tk, htk⟩ := (show sectionRingGrade L (k • e) from
      ⟨t.val ^ k, SetLike.pow_mem_graded k t.property⟩).property
    change DirectSum.of _ _ tn = t.val ^ n at htn
    change DirectSum.of _ _ tk = t.val ^ k at htk
    rw [← htn, ← htk, DirectSum.of_mul_of, DirectSum.of_eq_same,
      DirectSum.of_eq_same, DirectSum.of_eq_same]
    rfl
  dsimp only [p, r, p₀, r₀] at hpr
  rw [← hdeg] at hpr
  rw [hm, ← Hom.app_presheaf_map, tmulSection_map] at hpr
  exact hpr

end AlgebraicGeometry.Scheme.Modules
