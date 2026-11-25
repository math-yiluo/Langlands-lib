/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.LocalizedCohomologyMayerVietoris
import WeilConjectures.AlgebraicGeometry.CohomologySectionLocalizationGluingAux

/-! # Mayer--Vietoris gluing for localization of twisted cohomology

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, Mayer--Vietoris paragraph
(blueprint: lem-sc-invert-s-cohomology-gluing).
-/

@[expose] public section

universe uG

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- If the canonical degree-zero localization comparisons
`H^p_*(W,L,F)_(s) → H^p(W ⊓ S, F)`, `ξ/s^n ↦ s^(-n) ξ`, are isomorphisms for `W = U`, `V`
and `U ⊓ V` in every degree `p`, then so is the comparison for `W = U ⊔ V`.
`S` is the open `X_s`, identified by its underlying set. Each comparison is an additive
isomorphism `e` out of the fraction presentation `CohomologyFractionPresentation L F s p W`
(def-sc-cohomology-fraction-presentation), tied to the canonical map by the equation
`s^n · e(ξ/s^n) = ξ|_{W ⊓ S}`; since `s` trivializes `L` on `S`, this determines `e`.
Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, Mayer--Vietoris paragraph
(blueprint: lem-sc-invert-s-cohomology-gluing).

Proof:
1. Apply lem-sc-invert-s-cohomology-mayer-vietoris-diagram to `U ∪ V`. It gives a
commutative five-term diagram with exact rows in every degree: the upper row is the
localized degree-zero twisted cohomology sequence and the lower row is the ordinary
sequence on the nonvanishing opens. Localization and taking degree zero are exact.
2. The four outside vertical arrows are the comparisons on `U`, `V`, and `U ∩ V`
in adjacent degrees, with direct sums on `U` and `V`; these are isomorphisms by the
three hypotheses. Apply lem-weil-pbc-five-lemma to obtain the middle comparison
isomorphism on `U ∪ V`. In degree zero the sequence begins with zero groups, so
left exactness gives the same conclusion. This holds for every `p`. -/
theorem cohomologyFractionPresentation_gluing
    (X : Scheme.{uG}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (h_locU : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p V ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p V).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p V n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : V ⊓ S ≤ V))).app (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locUV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p (U ⊓ V) ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p (U ⊓ V) n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ V ⊓ S ≤ U ⊓ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ) :
    ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p (U ⊔ V) ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p ((U ⊔ V) ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊔ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p ((U ⊔ V) ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p (U ⊔ V) n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : (U ⊔ V) ⊓ S ≤ U ⊔ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ := by
  classical
  obtain ⟨S₀, hS₀, hIS, hUS, δ, hδ0, hδexact, hδnat, c, hc, a, b, d,
      ha, hbU, hbV, hd, hinj, hexact, hca, hcb, hcd⟩ :=
    AlgebraicGeometry.localizedCohomology_mayerVietoris X L F s U V hU hV
  have hEq : S = S₀ := by
    apply SetLike.ext
    intro x
    change x ∈ (S : Set X) ↔ x ∈ (S₀ : Set X)
    rw [hS, hS₀]
  subst S₀
  have hbij : ∀ p : ℕ, Function.Bijective (c (U ⊔ V) p) := by
    exact localized_middle_comparison_bijective X L s F S hS₀ U V hU hV c hc
      h_locU h_locV h_locUV
  intro p
  let e : CohomologyFractionPresentation L F s p (U ⊔ V) ≃+
      (RingedSpace.openModuleCohomology X.toRingedSpace p ((U ⊔ V) ⊓ S)).obj F :=
    AddEquiv.ofBijective (c (U ⊔ V) p) (hbij p)
  refine ⟨e, ?_⟩
  intro n ξ
  simpa [e] using hc (U ⊔ V) p n ξ

end AlgebraicGeometry.Scheme.Modules
