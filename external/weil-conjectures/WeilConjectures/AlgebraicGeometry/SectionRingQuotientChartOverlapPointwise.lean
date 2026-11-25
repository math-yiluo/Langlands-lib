/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import all WeilConjectures.AlgebraicGeometry.SectionRingProjPreimageForward
import all WeilConjectures.AlgebraicGeometry.SectionRingProjPreimageReverse

/-! # Underlying maps of section-ring quotient charts

Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-base-map-pointwise).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

-- Keep sections on their ambient images; only the scalar germ crosses the open immersion.
private theorem chart_mem_iff_nonvanishing
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (U : X.Opens) (g : U.toScheme ⟶ Proj (sectionRingGrade L))
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
    (x : U.toScheme) (d : ℕ) (hd : 0 < d) (s : sectionRingGrade L d)
    (hs : x.val ∈ nonvanishingLocus (L.tensorPow d) (s.val d))
    (r : ℕ) (hr : 0 < r) (a : sectionRingGrade L r) :
    g x ∈ Proj.basicOpen (sectionRingGrade L) a.val ↔
      x.val ∈ nonvanishingLocus (L.tensorPow r) (a.val r) := by
  constructor
  · intro hxa
    have hdeg : r • d = d • r := Nat.mul_comm r d
    let ξ : sectionRingGrade L (d • r) :=
      ⟨s.val ^ r, hdeg ▸ SetLike.pow_mem_graded r s.property⟩
    have hs' := (nonvanishing_power L s r hr x.val).mpr hs
    have hξ : x.val ∈ nonvanishingLocus (L.tensorPow (d • r)) (ξ.val (d • r)) := by
      dsimp only [ξ]
      rw [← hdeg]
      exact hs'
    have hp := nonvanishing_of_local_smul (L.tensorPow (d • r))
      ((a.val ^ d) (d • r)) (ξ.val (d • r))
      (U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val))
      (g.app (Proj.basicOpen (sectionRingGrade L) a.val)
        (Proj.awayToSection (sectionRingGrade L) a.val
          (HomogeneousLocalization.Away.mk (sectionRingGrade L) a.property d
            ξ.val ξ.property))) x.val ⟨x, hxa, rfl⟩ (hg r hr a d ξ) hξ
    exact (nonvanishing_power L a d hd x.val).mp hp
  · intro hxa
    obtain ⟨q, b, hq, hxb⟩ := exists_sectionRing_chart L (g x)
    have hdeg : q • r = r • q := Nat.mul_comm q r
    let ξ : sectionRingGrade L (r • q) :=
      ⟨a.val ^ q, hdeg ▸ SetLike.pow_mem_graded q a.property⟩
    have hξ : x.val ∈ nonvanishingLocus (L.tensorPow (r • q)) (ξ.val (r • q)) := by
      have hp := (nonvanishing_power L a q hq x.val).mpr hxa
      rw [hdeg] at hp
      exact hp
    let z := Proj.awayToSection (sectionRingGrade L) b.val
      (HomogeneousLocalization.Away.mk (sectionRingGrade L) b.property r ξ.val ξ.property)
    have hu : IsUnit (X.presheaf.germ
        (U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) b.val))
        x.val ⟨x, hxb, rfl⟩ (g.app (Proj.basicOpen (sectionRingGrade L) b.val) z)) :=
      scalar_isUnit_of_nonvanishing (L.tensorPow (r • q)) _ _ _
        (hg q hq b r ξ) x.val ⟨x, hxb, rfl⟩ hξ
    have hu' : IsUnit (U.toScheme.presheaf.germ
        (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) b.val) x hxb
        (g.app (Proj.basicOpen (sectionRingGrade L) b.val) z)) := by
      have hi := hu.map (U.stalkIso x).inv.hom
      have hgerm := CommRingCat.hom_ext_iff.mp
        (U.germ_stalkIso_inv (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) b.val) x hxb)
      exact (DFunLike.congr_fun hgerm _ ▸ hi)
    have hz : IsUnit ((Proj (sectionRingGrade L)).presheaf.germ
        (Proj.basicOpen (sectionRingGrade L) b.val) (g x) hxb z) := by
      apply (isUnit_map_iff (g.stalkMap x).hom _).mp
      rwa [g.germ_stalkMap_apply]
    have hnot := chart_fraction_numerator_notMem (sectionRingGrade L) b r ξ (g x) hxb hz
    rw [← Proj.basicOpen_pow (sectionRingGrade L) a.val q hq]
    exact hnot

-- Degree-zero tests follow by multiplying by a common positive-degree chart.
private theorem proj_eq_of_positive_chart_membership
    {X : Scheme.{v}} (L : X.Modules) [L.IsInvertible]
    (p q : Proj (sectionRingGrade L))
    (hpq : ∀ (r : ℕ) (_hr : 0 < r) (a : sectionRingGrade L r),
      p ∈ Proj.basicOpen (sectionRingGrade L) a.val ↔
        q ∈ Proj.basicOpen (sectionRingGrade L) a.val) : p = q := by
  obtain ⟨d, b, hd, hpb⟩ := exists_sectionRing_chart L p
  have hqb := (hpq d hd b).mp hpb
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro r a ha
  by_cases hr : 0 < r
  · exact not_iff_not.mp (hpq r hr ⟨a, ha⟩)
  · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    let c : sectionRingGrade L d :=
      ⟨a * b.val, by simpa only [zero_add] using SetLike.mul_mem_graded ha b.property⟩
    have hc := hpq d hd c
    change p ∈ Proj.basicOpen (sectionRingGrade L) (a * b.val) ↔
      q ∈ Proj.basicOpen (sectionRingGrade L) (a * b.val) at hc
    rw [Proj.basicOpen_mul] at hc
    have hc' : p ∈ Proj.basicOpen (sectionRingGrade L) a ↔
        q ∈ Proj.basicOpen (sectionRingGrade L) a := by
      simpa only [TopologicalSpace.Opens.mem_inf, hpb, hqb, and_true] using hc
    exact not_iff_not.mp hc'

/-- The underlying continuous maps of the restricted quotient charts agree.
Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-base-map-pointwise).

Proof: Fix x in U intersect V and a positive-degree homogeneous a of degree r.
This pointwise statement isolates the point comparison step from final function extensionality.
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
theorem sectionRing_overlap_base_map_pointwise
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
    ∀ x, (ConcreteCategory.hom (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).base) x =
      (ConcreteCategory.hom (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).base) x := by
  intro x
  let xu : U.toScheme := X.homOfLE (inf_le_left : U ⊓ V ≤ U) x
  let xv : V.toScheme := X.homOfLE (inf_le_right : U ⊓ V ≤ V) x
  have hxs : xu.val ∈ nonvanishingLocus (L.tensorPow d) (s.val d) := by
    rw [← hU]
    exact xu.property
  have hxt : xv.val ∈ nonvanishingLocus (L.tensorPow e) (t.val e) := by
    rw [← hV]
    exact xv.property
  change g xu = h xv
  apply proj_eq_of_positive_chart_membership L
  intro r hr a
  have hxval : xu.val = xv.val := by
    simp only [xu, xv, Scheme.homOfLE_apply]
  have hv := chart_mem_iff_nonvanishing X L V h hh xv e he t hxt r hr a
  rw [← hxval] at hv
  exact (chart_mem_iff_nonvanishing X L U g hg xu d hd s hxs r hr a).trans hv.symm


end AlgebraicGeometry.Scheme.Modules
