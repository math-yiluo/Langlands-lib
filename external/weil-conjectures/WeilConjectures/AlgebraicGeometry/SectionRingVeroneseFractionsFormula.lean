/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionKernel

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical Veronese fraction equivalence, constructed by the quotient map.
Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the proof of Lemma 01Q1.
(blueprint: lem-sc-section-ring-veronese-fractions-formula)

The explicit direct-sum map sends `t` in numerator degree `n` to
`of_(nd)(T_n⁻¹(t))/s^n`. Its surjectivity is proved in
`sectionRingVeroneseFractionMap_surjective`; its kernel is the relation submodule by
`sectionRingVeroneseFractionMap_kernel`. The first isomorphism theorem therefore
constructs a quotient equivalence from section fractions to homogeneous localization.
We take its inverse. The only inverse chosen is the unique inverse of this fixed
bijective quotient map. No data are chosen from a bare existence theorem.
-/
noncomputable def sectionRingVeroneseFractionEquiv
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) :=
  (QuotientAddGroup.liftEquiv
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup
    (sectionRingVeroneseFractionMap_surjective X L d s)
    (sectionRingVeroneseFractionMap_kernel X L d s)).symm

/-- Formula for the Veronese fraction equivalence on homogeneous generators.
Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
(blueprint: lem-sc-section-ring-veronese-fractions-formula)
Proof: apply the inverse of the constructed equivalence to both sides. The quotient
map sends the displayed section-fraction generator to the fraction whose numerator
is obtained by first applying `T_n` and then `T_n⁻¹`. These cancel. Membership of `ξ`
in the image of the degree `n*d` injection gives `of_(nd)(ξ_(nd)) = ξ`. Hence the
quotient map sends the generator to exactly `ξ/s^n`. Applying its inverse gives
the formula. The quotient map is the actual additive extension of the explicit
summand maps, so this computation does not use any generator formula as an assumption.
-/
theorem sectionRing_veronese_fraction_formula
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d)
    (e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d))
    (he : e = sectionRingVeroneseFractionEquiv X L d s) :
    ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        ξ.val ξ.property) =
      sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
        ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
          L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d))) := by
  subst e
  intro n ξ
  apply (sectionRingVeroneseFractionEquiv X L d s).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change _ = sectionRingVeroneseFractionMap X L d s
    (DirectSum.of
      (fun i : ℕ ↦ Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow i, ⊤)) n
      ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (ξ.val (n • d))))
  simp only [sectionRingVeroneseFractionMap, DirectSum.toAddMonoid_of,
    AddMonoidHom.comp_apply]
  rw [sectionRingVeroneseNumerator_cancel X L d n ξ]
  rfl

end AlgebraicGeometry.Scheme.Modules
