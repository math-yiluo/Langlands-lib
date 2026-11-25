/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Topology.ModuleMayerVietoris
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.CohomologyFractionComparison
import WeilConjectures.AlgebraicGeometry.CohomologyFractionMayerVietorisExact
import WeilConjectures.AlgebraicGeometry.CohomologyFractionMayerVietorisSquares

/-! # Mayer--Vietoris diagram for localized twisted cohomology

Source: Stacks Project, Cohomology of Schemes, Tag 09MR, Mayer--Vietoris paragraph
(blueprint: lem-sc-invert-s-cohomology-mayer-vietoris-diagram).
-/

@[expose] public section

universe uMV

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/-- The canonical comparison maps on fractions form a map of exact Mayer--Vietoris
sequences. Fractions are represented by the landed presentation `CohomologyFractionPresentation`
(def-sc-cohomology-fraction-presentation). The comparison `c` is tied by
`s^n · c(ξ/s^n) = ξ|_{W ⊓ S}`; since `s` trivializes `L` on `S`, this is the formula
ξ/s^n ↦ s^(-n) ξ and determines `c`. The connecting transformations `δ` are tied as
Mayer--Vietoris connecting maps of every module and every pair of opens: exactness of the
long sequence and compatibility with restriction to a smaller open (Tag 01EB).
The formulas on fractions specify the upper maps uniquely, including the connecting
maps. Exactness at degree zero is injectivity of `a 0`; thus H^(-1) is zero.

Source: Stacks, Tag 09MR, Mayer--Vietoris paragraph; Tags 01EB and 05QB
(blueprint: lem-sc-invert-s-cohomology-mayer-vietoris-diagram).

Proof: (1) Apply lem-sc-mayer-vietoris-open-cover to every twist. Naturality in the
module makes every map, including the boundary, commute with multiplication by s.
Take the direct sum over twists. Intersecting opens with the nonvanishing locus
preserves intersection and union. (2) Apply lem-sc-graded-localization-exact to
localize the exact graded sequence and take degree zero; the fraction presentation
is the same localization. (3) Apply the same Mayer--Vietoris sequence to the cover
on the nonvanishing open. Restriction and division by the trivializing section
commute with the boundary by naturality (lem-weil-pbc-right-derived-universal-delta-functor
and pqf-def-cohomology). Check every square on xi/s^n; these fractions generate. -/
theorem localizedCohomology_mayerVietoris (X : Scheme.{uMV}) [CompactSpace X]
    [QuasiSeparatedSpace X] (L F : X.Modules) [L.IsInvertible] [F.IsQuasicoherent]
    (s : Γ(L, ⊤)) (U V : X.Opens)
    (_hU : IsCompact (U : Set X)) (_hV : IsAffineOpen V) :
    ∃ S : X.Opens, (S : Set X) = nonvanishingLocus L s ∧
      (U ⊓ S) ⊓ (V ⊓ S) = (U ⊓ V) ⊓ S ∧
      (U ⊓ S) ⊔ (V ⊓ S) = (U ⊔ V) ⊓ S ∧
    ∃ δ : ∀ (A B : X.Opens) (p : ℕ),
      openModuleCohomology X.toRingedSpace p (A ⊓ B) ⟶
        openModuleCohomology X.toRingedSpace (p + 1) (A ⊔ B),
      (∀ (A B : X.Opens) (G : X.Modules),
        Function.Injective
          (fun x : (openModuleCohomology X.toRingedSpace 0 (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace 0
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace 0
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x))) ∧
      (∀ (A B : X.Opens) (G : X.Modules) (p : ℕ),
        Function.Exact
          (fun x : (openModuleCohomology X.toRingedSpace p (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x))
          (fun x : (openModuleCohomology X.toRingedSpace p A).obj G ×
              (openModuleCohomology X.toRingedSpace p B).obj G =>
            (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_left : A ⊓ B ≤ A))).app G x.1 -
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_right : A ⊓ B ≤ B))).app G x.2) ∧
        Function.Exact
          (fun x : (openModuleCohomology X.toRingedSpace p A).obj G ×
              (openModuleCohomology X.toRingedSpace p B).obj G =>
            (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_left : A ⊓ B ≤ A))).app G x.1 -
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_right : A ⊓ B ≤ B))).app G x.2)
          ((δ A B p).app G) ∧
        Function.Exact ((δ A B p).app G)
          (fun x : (openModuleCohomology X.toRingedSpace (p + 1) (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace (p + 1)
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace (p + 1)
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x))) ∧
      (∀ (A B T : X.Opens) (p : ℕ),
        δ A B p ≫ openModuleCohomologyRestriction X.toRingedSpace (p + 1)
            (homOfLE (sup_le_sup inf_le_left inf_le_left)) =
          openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE (inf_le_inf inf_le_left inf_le_left)) ≫
            δ (A ⊓ T) (B ⊓ T) p) ∧
    ∃ c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F,
      (∀ (W : X.Opens) (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules)),
        (openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (c W p (cohomologyFraction L F s p W n ξ)) =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : W ⊓ S ≤ W))).app (F ⊗ L.tensorPow n : X.Modules) ξ) ∧
    ∃ (a : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊔ V) →+
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V)
      (b : ∀ p : ℕ,
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V →+
          CohomologyFractionPresentation L F s p (U ⊓ V))
      (d : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊓ V) →+
        CohomologyFractionPresentation L F s (p + 1) (U ⊔ V)),
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊔ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        a p (cohomologyFraction L F s p (U ⊔ V) n ξ) =
          (cohomologyFraction L F s p U n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ),
          cohomologyFraction L F s p V n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ))) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (cohomologyFraction L F s p U n ξ, 0) = cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p V).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (0, cohomologyFraction L F s p V n ξ) = -cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        d p (cohomologyFraction L F s p (U ⊓ V) n ξ) =
          cohomologyFraction L F s (p + 1) (U ⊔ V) n
            ((δ U V p).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      Function.Injective (a 0) ∧
      (∀ p : ℕ, Function.Exact (a p) (b p) ∧ Function.Exact (b p) (d p) ∧
        Function.Exact (d p) (a (p + 1))) ∧
      (∀ (p : ℕ) (x : CohomologyFractionPresentation L F s p (U ⊔ V)),
        c U p (a p x).1 =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S le_sup_left))).app F (c (U ⊔ V) p x) ∧
        c V p (a p x).2 =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S le_sup_right))).app F (c (U ⊔ V) p x)) ∧
      (∀ (p : ℕ)
        (x : CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V),
        c (U ⊓ V) p (b p x) =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S inf_le_left))).app F (c U p x.1) -
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S inf_le_right))).app F (c V p x.2)) ∧
      (∀ (p : ℕ) (x : CohomologyFractionPresentation L F s p (U ⊓ V)),
        c (U ⊔ V) (p + 1) (d p x) =
          (openModuleCohomologyRestriction X.toRingedSpace (p + 1)
            (homOfLE (inf_sup_right U V S).le)).app F
            ((δ (U ⊓ S) (V ⊓ S) p).app F
              ((openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_inf_distrib_right U V S).ge)).app F
                  (c (U ⊓ V) p x)))) := by
  obtain ⟨S, hS, -, -⟩ := nonvanishing_section_trivializes X L s
  obtain ⟨δ, hinj, hexact, hrestrict⟩ := module_mayerVietoris X.toRingedSpace
  obtain ⟨c, hc⟩ := exists_cohomologyFraction_comparison X L F s S hS
  obtain ⟨a, b, d, ha, hbU, hbV, hd, hainj, hab⟩ :=
    exists_cohomologyFraction_mayerVietoris_exact X L F s U V δ hinj hexact
  obtain ⟨hca, hcb, hcd⟩ := cohomologyFraction_mayerVietoris_squares
    X L F s U V S hS δ hrestrict c hc a b d ⟨ha, hbU, hbV, hd⟩
  exact ⟨S, hS, (inf_inf_distrib_right U V S).symm, (inf_sup_right U V S).symm,
    δ, hinj, hexact, hrestrict, c, hc,
    a, b, d, ha, hbU, hbV, hd, hainj, hab, hca, hcb, hcd⟩

end AlgebraicGeometry
