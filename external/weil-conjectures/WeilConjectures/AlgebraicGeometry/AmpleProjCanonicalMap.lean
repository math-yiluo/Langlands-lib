/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.AmpleProjPreimage
import WeilConjectures.AlgebraicGeometry.AmpleProjChartFormula

/-!
# The canonical morphism to Proj of the section ring

Source: Stacks Project, Properties, Tag 01PZ, existence and clause (1), and Constructions,
Tag 01N8, the localized chart formula (blueprint: lem-sc-ample-proj-canonical-map).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical morphism to the Proj of the section ring, with its inverse images and
its map on chart sections. Source: Stacks Project, Tags 01PZ and 01N8
(blueprint: lem-sc-ample-proj-canonical-map).

Step 1: a positive-degree section `s` trivializes its tensor power on its nonvanishing
open (lem-weil-pbc-nonvanishing-section-trivializes). Dividing a homogeneous numerator of
degree `n * deg(s)` by `s^n` defines a ring map out of the degree-zero homogeneous
localization. The affine morphism correspondence (lem-weil-pbc-morphism-into-affine-scheme)
and the Proj chart isomorphism (def-pc-proj) give the local morphism.

Step 2: for sections of degrees `d` and `e`, the chart function `t^d / s^e` is invertible
exactly on the intersection of their nonvanishing opens. The two localized ring maps
agree there: both send `a / (st)^n` to the quotient by the section `(st)^n`. Thus their
morphisms to the affine chart `D_+(st)` agree by the affine morphism correspondence.

Step 3: the assumed cover and this overlap agreement glue the local morphisms
(lem-weil-pbc-scheme-morphism-gluing).

Step 4: on a chart for `t`, membership in the inverse image of `D_+(s)` is invertibility
of `s^e / t^d`. Since `t` trivializes its power, this is exactly nonvanishing of `s`.
This proves the inverse-image equality. The chart sections map is the ring map of Step 1.
The fraction formula below is written without division: its value times the trivializing
section `s^n` equals the numerator. Multiplication by this section is bijective, so this
is precisely the quotient `s^{-n} ξ`, including when the nonvanishing open is empty. -/
theorem exists_sectionRing_proj_morphism (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (hcover : ∀ x : X, ∃ (d : ℕ) (s : sectionRingGrade L d),
      0 < d ∧ x ∈ nonvanishingLocus (L.tensorPow d) (s.val d)) :
    ∃ f : X ⟶ Proj (sectionRingGrade L),
      ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade L d),
        (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val : Set X) =
          nonvanishingLocus (L.tensorPow d) (s.val d) ∧
        ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
          (f.app (Proj.basicOpen (sectionRingGrade L) s.val)
            (Proj.awayToSection (sectionRingGrade L) s.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
              ((s.val ^ n) (n • d)) =
          (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
            (ξ.val (n • d)) := by
  obtain ⟨f, hformula⟩ := exists_sectionRing_proj_chart_formula X L hcover
  refine ⟨f, ?_⟩
  intro d hd s
  refine ⟨?_, hformula d hd s⟩
  ext x
  exact sectionRing_proj_mem_basicOpen X L f hformula x (hcover x) d hd s

end AlgebraicGeometry.Scheme.Modules
