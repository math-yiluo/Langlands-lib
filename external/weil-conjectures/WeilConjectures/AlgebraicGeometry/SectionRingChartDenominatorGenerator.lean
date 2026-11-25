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
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes

/-! # Free denominators on inverse images of section-ring charts

Source: Stacks Project, Tags 01N8 and 01NK, uniqueness arguments, and Tag 01CY.
(blueprint: lem-sc-section-ring-chart-denominator-generator).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an inverse homogeneous chart, each power of the denominator is a free generator.
Source: Stacks Project, Tags 01N8 and 01NK, uniqueness proofs; Tag 01CY.
(blueprint: lem-sc-section-ring-chart-denominator-generator).

Proof: At a point of Q, s is nonvanishing because Q lies in U. Apply the fraction
identity with denominator a, exponent d and numerator s^r, and take its value in the
fibre. Tensor products of nonzero vectors in one-dimensional vector spaces are
nonzero, so s^r is nonzero. The identity forces a^d to be nonzero, hence a to be
nonvanishing. Tag 01CY trivializes L^{tensor r} by a on its nonvanishing locus.
Positive section-ring powers have the same nonvanishing locus: on simultaneous
trivializations, tensor multiplication multiplies the coefficients, and D(f*g)
is D(f) intersect D(g); tensorPowAddIso transports this tensor section to the
section-ring product. Induction proves power invariance. Thus a^n is nonvanishing
on Q for n>0. Apply Tag 01CY to a^n and restrict to Q. Its unique-quotient clause
proves both injectivity and surjectivity on every smaller open. For n=0 use the
restriction of the tensor-unit generator, independently of a. The argument is valid
on nonreduced schemes because it uses fibre values to
locate the trivialization, and then the module isomorphism itself. On the empty
open the unique module and scalar sections give the same bijection. -/
theorem sectionRing_chart_denominator_generator
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
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
    (r : ℕ) (a : sectionRingGrade L r) (hr : 0 < r)
    (Q : X.Opens)
    (hQ : Q ≤ U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val)) :
    ∀ n : ℕ, IsFreeGenerator
      ((L.tensorPow (n • r)).presheaf.map (homOfLE (le_top : Q ≤ ⊤)).op
        ((a.val ^ n) (n • r))) := by
  have ha (x : X) (hx : x ∈ Q) :
      x ∈ nonvanishingLocus (L.tensorPow r) (a.val r) := by
    have hx' := hQ hx
    have hs : x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) := by
      rw [← hU]
      exact U.ι_image_le _ hx'
    have hdeg : r • d = d • r := Nat.mul_comm r d
    let ξ : sectionRingGrade L (d • r) :=
      ⟨s.val ^ r, hdeg ▸ SetLike.pow_mem_graded r s.property⟩
    have hξ : x ∈ nonvanishingLocus (L.tensorPow (d • r)) (ξ.val (d • r)) := by
      dsimp only [ξ]
      rw [← hdeg]
      exact (nonvanishing_power L s r hr x).mpr hs
    have hpow := nonvanishing_of_local_smul (L.tensorPow (d • r))
      ((a.val ^ d) (d • r)) (ξ.val (d • r))
      (U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val))
      (g.app (Proj.basicOpen (sectionRingGrade L) a.val)
        (Proj.awayToSection (sectionRingGrade L) a.val
          (HomogeneousLocalization.Away.mk (sectionRingGrade L) a.property d
            ξ.val ξ.property))) x hx' (hg r hr a d ξ) hξ
    exact (nonvanishing_power L a d hd x).mp hpow
  intro n
  by_cases hn : n = 0
  · subst n
    have hzero : (0 : ℕ) • r = 0 := zero_smul ℕ r
    rw [hzero]
    simp only [pow_zero, DirectSum.one_def, DirectSum.of_eq_same]
    change IsFreeGenerator ((Modules.unit X).presheaf.map (homOfLE le_top).op
      (unitSectionsEquiv ⊤ 1))
    convert (isFreeGenerator_one (⊤ : X.Opens)).map (le_top : Q ≤ ⊤) using 1
    rfl
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨T, hT, -, hquot⟩ := nonvanishing_section_trivializes X (L.tensorPow (n • r))
      ((a.val ^ n) (n • r))
    have hQT : Q ≤ T := by
      intro x hx
      change x ∈ (T : Set X)
      rw [hT]
      exact (nonvanishing_power L a n hn' x).mpr (ha x hx)
    intro W hW
    simp only [presheaf_map_map_apply]
    constructor
    · intro c b hcb
      obtain ⟨u, hu, huniq⟩ := hquot W (hW.trans hQT)
        (c • (L.tensorPow (n • r)).presheaf.map (homOfLE le_top).op
          ((a.val ^ n) (n • r)))
      exact (huniq c rfl).trans (huniq b hcb).symm
    · intro z
      obtain ⟨c, hc, -⟩ := hquot W (hW.trans hQT) z
      exact ⟨c, hc.symm⟩

end AlgebraicGeometry.Scheme.Modules
