/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTrace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
public import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # The two Chern components of the projective-line diagonal

Source: blueprint lemma-class-diagonal-projective-line, standard-chart Cartier calculation;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport

/-- The short relative-Cartier proof used by diagonalImmersion_cartier.
Source: proposition-ell-adic-cycle-class-diagonal, Cartier clause;
theorem-hilbert-schemes-points-smooth-curve--1. -/
private theorem finiteP1_diagonal_cartier (S : Scheme.{u}) :
    (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible := by
  let d := pullback.diagonal (ProjectiveLine S ↘ S)
  let p := pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
  let j := d.ker.subschemeι
  have hker : d.ker = j.ker := by simp [j]
  let e := IsClosedImmersion.lift d j hker.le
  have : IsIso e := IsClosedImmersion.isIso_lift d j hker
  have he : e ≫ d = j := IsClosedImmersion.lift_fac d j hker.le
  have hp : j ≫ p = e := by
    rw [← he, Category.assoc]
    simp only [d, p, pullback.diagonal_fst, Category.comp_id]
  have : IsIso (j ≫ p) := hp.symm ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    (J := d.ker) inferInstance inferInstance inferInstance

/-- The Cartier diagonal has a supported Kummer boundary and its two Chern components.
Source: blueprint lemma-class-diagonal-projective-line, standard-chart proof;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
(auxiliary; not a blueprint node)

Proof: the short relative-Cartier argument of diagonalImmersion_cartier proves the
diagonal ideal invertible over any base
using the relative Cartier criterion for a section of the smooth projective-line
projection. supported_cartier_boundary_existsUnique gives its actual uniquely
normalized supported boundary. Apply ordinaryFiniteP1_diagonal_kummer_component_formula
to this boundary and the supplied relative hyperplane class. This gives the two
components before any splitting or trace is chosen. -/
theorem ordinaryFiniteP1_diagonal_chern_components (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (hPP : IsUnit (N : Γ(ProjectiveLine (ProjectiveLine S), ⊤)))
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S) hPP c) :
    ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
      ∃ κ : Ext
        ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
        SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S))
          hI hW κ ∧
        ∀ a : Bool, ∃ β : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
              (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
            ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
              ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
            β ≫ ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP +
              ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) c  := by
  let hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible :=
    finiteP1_diagonal_cartier S
  obtain ⟨κ, hκ, _⟩ := supported_cartier_boundary_existsUnique
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hW
    (pullback.diagonal (ProjectiveLine S ↘ S)) hI
  exact ⟨hI, κ, hκ,
    ordinaryFiniteP1_diagonal_kummer_component_formula N hN A hA t S hS
      hP hPP hW c hc hI κ hκ⟩

end AlgebraicGeometry.Etale
