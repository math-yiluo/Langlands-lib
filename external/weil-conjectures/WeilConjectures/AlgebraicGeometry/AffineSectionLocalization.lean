/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization

/-!
# Degree-zero localization of sections on an affine scheme

Source: Stacks Project, Properties, Lemma 01PW, equation module-invert-s; Cohomology of
Schemes, Lemma 09MR, affine case (blueprint: lem-sc-affine-section-localization).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme the canonical map from degree-zero section fractions to sections on
the nonvanishing open `Y_s` is an isomorphism. The fraction formula is written without
choosing an inverse tensor power: `e(t/s^n) ⊗ s^n = t|_U`, i.e. `e(t/s^n) = s⁻ⁿt`.
Scalar compatibility (scalars restricted along `Γ(Y, O_Y) → Γ(U, O_Y)`) makes it an
isomorphism of modules. The domain is the existing fraction presentation of the degree-zero
localization (def-sc-section-fraction-presentation).

Source: Stacks Properties, Lemma 01PW (2), equation module-invert-s, and Cohomology of
Schemes, Lemma 09MR, affine case (blueprint: lem-sc-affine-section-localization).
Proof: (1) An affine scheme is quasi-compact and quasi-separated by
lem-weil-pbc-affine-scheme-qcqs. (2) Apply lem-sc-p1-invertible-section-localization with
`X = Y`; its invertible module, quasi-coherent module, section, nonvanishing locus and
canonical fraction map are exactly these data. -/
theorem affine_section_localization
    (Y : Scheme.{u}) [IsAffine Y]
    (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : Y.Modules) [F.IsQuasicoherent] :
    ∃ U : Y.Opens, (U : Set Y) = nonvanishingLocus L s ∧
      ∃ e : SectionFractionPresentation L F s ≃+ Γ(F, U),
        (∀ (r : Γ(Y, ⊤)) (z : SectionFractionPresentation L F s),
          e (r • z) = (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • e z) ∧
        (∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)),
          tmulSection (e (sectionFraction L F s n t))
              (tensorPowSectionOne (homOfGlobalSection L s) n U) =
            (F ⊗ L.tensorPow n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t) := by
  exact exists_sectionFraction_nonvanishing_equiv Y L s F

end AlgebraicGeometry.Scheme.Modules
