/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapBase
import WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf

/-! # Uniqueness of section-ring quotient charts on overlaps

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Two morphisms satisfying the homogeneous fraction equations agree on the overlap
of their nonvanishing source opens. This is a comparison theorem for given morphisms;
it asserts no existence of quotient charts.
Source: Stacks Project, Constructions, Tags 01N8 (lemma-converse-construction),
01NK (lemma-invertible-map-into-proj), overlap and uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap).

Proof: First show that g sends U into D_+(s). At x in U choose a positive-degree
chart D_+(a) through g(x), say a has degree r. Apply hg with denominator a,
exponent d and numerator s^r. In the one-dimensional residue-field fibre, s^r is
nonzero. Thus both the value of a^d and the pulled-back coefficient of s^r/a^d
are nonzero. The coefficient is therefore a unit in the source local ring. Since
the stalk homomorphism is local, s^r/a^d is a unit in the target local ring;
the homogeneous localization unit criterion gives s outside the homogeneous prime.
More generally the same argument shows that a nonvanishing section t has image in
D_+(t). In particular g and h both send U intersect V into D_+(st).

Factor the restrictions through this affine chart. The section st is a generator
of L^{tensor(d+e)} on U intersect V, and every positive tensor power is again a
free generator. Restrict hg and hh with denominator st to U intersect V. For every
homogeneous numerator xi of degree n(d+e), their two scalar pullbacks multiplied
by the same generator (st)^n equal the same restriction of xi. Cancel the generator
to get equality of the scalar pullbacks. Every element of S_(st) is such a fraction,
so the ring maps agree. The affine morphism correspondence gives equality of the
factored morphisms, and composing the chart inclusion gives the displayed equality.
When n = 0 the generator is the tensor unit; an empty overlap has unique sections
and morphisms. No reducedness, affineness of U or V, or covering hypothesis is used. -/
theorem sectionRing_quotient_charts_overlap
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d e : ℕ) (s : sectionRingGrade L d) (t : sectionRingGrade L e)
    (hd : 0 < d) (he : 0 < e) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (hV : (V : Set X) = nonvanishingLocus (L.tensorPow e) (t.val e))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (h : V.toScheme ⟶ Proj (sectionRingGrade L))
    (hg : ∀ (e : ℕ), 0 < e → ∀ (t : sectionRingGrade L e)
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
    (hh : ∀ (e : ℕ), 0 < e → ∀ (t : sectionRingGrade L e)
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
    X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h := by
  have hbase := sectionRing_overlap_base_map X L d e s t hd he U V hU hV g h hg hh
  apply Scheme.Hom.ext hbase
  exact sectionRing_overlap_sheaf_map X L d s hd U V hU g h hg hh hbase

end AlgebraicGeometry.Scheme.Modules
