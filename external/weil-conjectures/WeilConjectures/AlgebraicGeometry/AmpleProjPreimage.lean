/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingProjPreimageForward
import WeilConjectures.AlgebraicGeometry.SectionRingProjPreimageReverse

/-! # Detecting nonvanishing from the section-ring chart formula

Source: Stacks Project, Constructions, Tag 01N8, chart inverse-image calculation;
Properties, Tag 01PZ, clause (1).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The fraction formula detects basic-open membership at a point outside the base locus.
Only this point must have a nonvanishing positive-degree section; no global cover is assumed.
Source: Stacks Project, Constructions, Tag 01N8, chart inverse-image calculation;
Properties, Tag 01PZ, clause (1)
(blueprint: lem-sc-ample-proj-canonical-map-preimage).

Proof: Work in the residue field at x, trivializing L near x. If f(x) is in D_+(s), choose
by hx a nonvanishing section t of degree e. Apply the fraction identity on this chart with
numerator t^d and denominator s^e. If s vanished at x, its e-th tensor power would vanish,
whereas the d-th power of t would not; the identity is a contradiction. Thus s does not
vanish. Conversely, suppose s is nonvanishing at x. Choose a positive-degree homogeneous
t with f(x) in D_+(t), possible because these opens cover Proj. The identity with numerator
s^e and denominator t^d first implies that t is nonvanishing at x, and then that the
pullback of s^e/t^d has nonzero residue. A scheme morphism induces a local homomorphism on
stalks, so this chart function is a unit at f(x). Its basic open in D_+(t) is exactly
D_+(s) intersect D_+(t), proving f(x) is in D_+(s). Positive powers preserve nonvanishing
in a one-dimensional residue-field fibre, which justifies both power tests. The argument
is pointwise and is vacuous for the empty scheme; a zero section gives both sides false. -/
theorem sectionRing_proj_mem_basicOpen (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (f : X ⟶ Proj (sectionRingGrade L))
    (hformula : ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade L d),
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
            (ξ.val (n • d)))
    (x : X)
    (hx : ∃ (e : ℕ) (t : sectionRingGrade L e),
      0 < e ∧ x ∈ nonvanishingLocus (L.tensorPow e) (t.val e))
    (d : ℕ) (hd : 0 < d) (s : sectionRingGrade L d) :
    x ∈ f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ↔
      x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) := by
  constructor
  · exact sectionRing_proj_mem_basicOpen_forward X L f hformula x hx d hd s
  · exact sectionRing_proj_mem_basicOpen_reverse X L f hformula x hx d hd s

end AlgebraicGeometry.Scheme.Modules
