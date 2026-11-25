/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
import WeilConjectures.AlgebraicGeometry.AffineOpenCohomologyLocalization
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.CohomologySectionLocalizationGluing
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction

/-! # Localization of graded cohomology at a section

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR
(blueprint: lem-sc-invert-s-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical degree-zero localization comparison is an isomorphism.
The displayed equation specifies the canonical map: multiplying the image of ξ/s^n
by the trivializing section s^n gives the restriction of ξ. Since s trivializes L
on U, this equation determines the map uniquely; an arbitrary isomorphism does not suffice.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR
(blueprint: lem-sc-invert-s-cohomology).

1. On an affine open, positive cohomology vanishes on both sides and degree zero is
   localization of sections (lem-sc-invert-s-cohomology-affine-case).
2. The restriction-and-division maps form a map of Mayer--Vietoris exact sequences.
   Principal opens commute with intersections and unions; localization and passage to
   degree zero are exact. The five-lemma proves gluing from U, V and U ∩ V
   (lem-sc-invert-s-cohomology-gluing).
3. Apply induction over quasi-compact opens to the property that all these comparisons
   are isomorphisms (lem-sc-invert-s-cohomology-induction), and take the whole space.
-/
theorem invertS_cohomology
    (X : Scheme.{u}) (L F : X.Modules) [L.IsInvertible]
    [F.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(L, ⊤)) (p : ℕ) :
    ∃ U : X.Opens, (U : Set X) = nonvanishingLocus L s ∧
      ∃ e : CohomologyFractionPresentation L F s p ⊤ ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F,
        ∀ (n : ℕ) (ξ :
          (RingedSpace.openModuleCohomology X.toRingedSpace p ⊤).obj
            (F ⊗ L.tensorPow n : X.Modules)),
          (RingedSpace.openModuleCohomology X.toRingedSpace p U).map
              (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                F ⟶ (F ⊗ L.tensorPow n : X.Modules))
              (e (cohomologyFraction L F s p ⊤ n ξ)) =
            (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE (le_top : U ≤ ⊤))).app (F ⊗ L.tensorPow n : X.Modules) ξ := by
  obtain ⟨S, hS, _, _⟩ := nonvanishing_section_trivializes X L s
  let P : X.Opens → Prop := fun U ↦
    ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app (F ⊗ L.tensorPow n : X.Modules) ξ
  have hAffine : ∀ U : X.Opens, IsAffineOpen U → P U := by
    intro U hU
    exact affineOpen_cohomology_localization X L s F S hS U hU
  have hUnion : ∀ (U V : X.Opens), IsCompact (U : Set X) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V) := by
    intro U V hU hV hPU hPV hPUV
    exact cohomologyFractionPresentation_gluing X L s F S hS U V hU hV hPU hPV hPUV
  have hTop : P ⊤ := quasiCompactOpen_induction X P hAffine hUnion ⊤ isCompact_univ
  let Q : X.Opens → Prop := fun T ↦
    ∃ e : CohomologyFractionPresentation L F s p ⊤ ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p T).obj F,
        ∀ (n : ℕ) (ξ :
          (RingedSpace.openModuleCohomology X.toRingedSpace p ⊤).obj
            (F ⊗ L.tensorPow n : X.Modules)),
          (RingedSpace.openModuleCohomology X.toRingedSpace p T).map
              (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                F ⟶ (F ⊗ L.tensorPow n : X.Modules))
              (e (cohomologyFraction L F s p ⊤ n ξ)) =
            (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE (le_top : T ≤ ⊤))).app (F ⊗ L.tensorPow n : X.Modules) ξ
  have h : Q (⊤ ⊓ S) := hTop p
  have h' : Q S := (congrArg Q (top_inf_eq S)) ▸ h
  exact ⟨S, hS, h'⟩

end AlgebraicGeometry.Scheme.Modules
