/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingCoefficientData

/-! # Coefficients in a homogeneous localization of a section ring

Source: Stacks Project, Constructions, Tag 01N8, local quotient construction.
(blueprint: lem-sc-section-ring-coefficient-hom).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A section generating its tensor power on an open defines the coefficient ring map.
Source: Stacks Project, Constructions, Tag 01N8, proof, local quotient construction.
(blueprint: lem-sc-section-ring-coefficient-hom).

Proof: Tensoring the free generator s on U gives a free generator s^n of L^{tensor nd}.
For a homogeneous numerator a in degree nd, let its coefficient be the unique scalar c
such that a|U = c (s^n)|U. Define the value of a/s^n to be c. If two fractions agree,
there is k with s^k (a s^m - b s^n) = 0. Restricting to U and expressing each term
in the free generator s^{k+n+m} gives equality of the two coefficients. This proves
well-definedness on the homogeneous localization quotient. The coefficient of 1/1 is
1; addition of fractions uses denominator s^{n+m} and adds coefficients; multiplication
uses tensor multiplication and multiplies coefficients. These computations give the
unital ring homomorphism and the asserted numerator equation. Degree zero uses the
canonical tensor unit. The empty open has singleton section types, so the same
construction is the unique ring map to the zero ring. -/
theorem exists_sectionRing_coefficient_hom
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d))) :
    ∃ ρ : HomogeneousLocalization.Away (sectionRingGrade L) s.val →+* Γ(X, U),
      ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        ρ (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
            ξ.val ξ.property) •
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (ξ.val (n • d)) := by
  obtain ⟨c, hc0, hc1, hcadd, hcmul, hcoef⟩ :=
    exists_sectionRing_coefficient_data X L d s hd U hs
  let ρ : HomogeneousLocalization.Away (sectionRingGrade L) s.val →+* Γ(X, U) :=
    { toFun := c
      map_one' := hc1
      map_mul' := hcmul
      map_zero' := hc0
      map_add' := hcadd }
  exact ⟨ρ, hcoef⟩

end AlgebraicGeometry.Scheme.Modules
