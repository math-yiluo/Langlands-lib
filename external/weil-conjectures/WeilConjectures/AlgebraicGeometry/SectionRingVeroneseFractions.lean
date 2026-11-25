/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionsCore
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionsFormula

/-! # Homogeneous section-ring fractions and Veronese section fractions

Source: Stacks Project, Properties, Tag 0B5L (equation module-invert-s),
Lemma 01PW(2), and the proof of Lemma 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Homogeneous localization of the section ring at a section of degree `d` is the
additive presentation of fractions for the invertible module `L.tensorPow d`.
Source: Stacks Project, Properties, Tag 0B5L (equation module-invert-s),
Lemma 01PW(2), and the proof of Lemma 01Q1.
(blueprint: lem-sc-section-ring-veronese-fractions).

Proof: identify the degree `n • d` summand with sections of
`(L.tensorPow d).tensorPow n` using `n • d = d * n` and `tensorPowMulIso`, and insert
the structure-module factor with the inverse left unitor. Send the resulting
numerator in the `n`-th summand to its fraction with denominator `s^n`. Tensor-power
coherence identifies the transition `t ↦ t tensor s^b` with multiplication by the
homogeneous ring element `s^b`. These transitions generate the relations in both
presentations. Indeed, every homogeneous fraction has a representative with denominator
`s^n`; two such representatives are equal exactly when their cross products agree after
multiplication by a further power of `s`. Move both to this common denominator to obtain
precisely the section-fraction relations. Conversely each transition gives equal
localization fractions. These maps are additive, descend to the quotients, and are inverse
on every homogeneous fraction and every summand generator. Zero or nilpotent `s` causes
both presentations to be zero, by the same transition relations. No positive-degree or
compactness hypothesis is needed for this algebraic identification.
-/
theorem exists_sectionRing_veronese_fraction_equiv
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    ∃ e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
        SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d),
      ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property) =
        sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
          ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
            L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d))) := by
  let e := sectionRingVeroneseFractionEquiv X L d s
  exact ⟨e, sectionRing_veronese_fraction_formula X L d s e rfl⟩

end AlgebraicGeometry.Scheme.Modules
