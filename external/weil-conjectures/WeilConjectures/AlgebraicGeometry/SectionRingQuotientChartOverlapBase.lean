/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapPointwise

/-! # Underlying maps of section-ring quotient charts

Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-base-map).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The underlying continuous maps of the restricted quotient charts agree.
Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-base-map).

Proof: Fix x in U intersect V and a positive-degree homogeneous a of degree r.
We show that g(x) belongs to D_+(a) if and only if a is nonvanishing at x.
For the forward implication, apply hg on the a-chart to n = d and numerator s^r,
whose degree is r*d = d*r. Since s is nonvanishing at x, its positive power s^r
has nonzero image in the residue-field fibre of L^{tensor(rd)}. Taking germs in
the equation shows that a^d cannot vanish in this fibre; hence a is nonvanishing.
For the reverse implication choose a positive-degree homogeneous b of degree q
with g(x) in D_+(b); such b exists since a Proj prime avoids the irrelevant ideal.
Apply hg with denominator b, exponent r and numerator a^q. The numerator has
nonzero fibre value. Thus the scalar pullback of a^q/b^r is outside the maximal
ideal of the source stalk, hence is a unit. The stalk homomorphism is local and
reflects units. In homogeneous localization at g(x), a fraction is a unit only
if its numerator avoids the homogeneous prime. Hence a^q, and therefore a,
avoids that prime, proving g(x) in D_+(a). The same argument with hh and t
proves the equivalence for h(x). Positive powers preserve nonvanishing because
one can trivialize L at x and test powers of a scalar in its residue field.
Ambient-image restrictions in hg and hh give exactly these germs under the
open-immersion stalk identifications. The two images therefore belong to the
same positive homogeneous basic opens. These form a topological basis for Proj;
Proj is T0, so the images are equal. Pointwise equality gives equality of the
continuous maps. If the overlap is empty there are no points to check. Zero or
nilpotent sections have empty nonvanishing loci and cause no excluded case. -/
theorem sectionRing_overlap_base_map
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d e : ℕ) (s : sectionRingGrade L d) (t : sectionRingGrade L e)
    (hd : 0 < d) (he : 0 < e) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (hV : (V : Set X) = nonvanishingLocus (L.tensorPow e) (t.val e))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (h : V.toScheme ⟶ Proj (sectionRingGrade L))
    (hg : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            g.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e)))
    (hh : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, V.ι ''ᵁ (h ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            h.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e))) :
    (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).base =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).base := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact sectionRing_overlap_base_map_pointwise X L d e s t hd he U V hU hV g h hg hh x

end AlgebraicGeometry.Scheme.Modules
