/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Torsion étale cohomological dimension

A scheme `X` has torsion étale cohomological dimension at most `c`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE X c`) if `Hᵠ(X_ét, F) = 0` for
every torsion abelian étale sheaf `F` on `X` and every `q > c`. For a field `K` this is the
condition `cd_tor(K) ≤ c` on `Spec K`.

The torsion étale cohomological dimension `cd(X) ∈ ℕ∞` is
`AlgebraicGeometry.Scheme.torsionCohomologicalDimension`, the least such `c` (or `⊤`); its
relative version for a morphism `f`, defined by the vanishing of the higher direct images
`Rᵠf_* F` of torsion sheaves, is
`AlgebraicGeometry.Scheme.Hom.torsionCohomologicalDimension`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Etale torsion cohomological dimension bound.

`cd_tor(X) ≤ c`: the étale cohomology `Hᵠ(X_ét, F)` vanishes for every torsion abelian étale
sheaf `F` on `X` and every `q > c`. -/
def HasTorsionCohomologicalDimensionLE (X : Scheme.{u}) (c : ℕ) : Prop :=
  ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
    ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q)

lemma HasTorsionCohomologicalDimensionLE.mono {X : Scheme.{u}} {c d : ℕ}
    (h : X.HasTorsionCohomologicalDimensionLE c) (hcd : c ≤ d) :
    X.HasTorsionCohomologicalDimensionLE d :=
  fun F hF q hq ↦ h F hF q (lt_of_le_of_lt hcd hq)

/-- Cohomological dimension.

The torsion étale cohomological dimension `cd(X) ∈ ℕ∞` of a scheme `X`: the least `d` with
`Hᵠ(X_ét, F) = 0` for every torsion abelian étale sheaf `F` and every `q > d`, and `⊤` if no such
`d` exists. -/
noncomputable def torsionCohomologicalDimension (X : Scheme.{u}) : ℕ∞ :=
  ⨅ (d : ℕ) (_ : X.HasTorsionCohomologicalDimensionLE d), (d : ℕ∞)

/-- `cd(X) ≤ c` if and only if `Hᵠ(X_ét, F) = 0` for all torsion `F` and `q > c`. -/
lemma torsionCohomologicalDimension_le_iff {X : Scheme.{u}} {c : ℕ} :
    X.torsionCohomologicalDimension ≤ c ↔ X.HasTorsionCohomologicalDimensionLE c := by
  refine ⟨fun h ↦ ?_, fun h ↦ iInf₂_le c h⟩
  by_contra hc
  have : (c : ℕ∞) < X.torsionCohomologicalDimension := by
    refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self c)) (le_iInf₂ fun d hd ↦ ?_)
    exact WithTop.coe_le_coe.2 (Nat.succ_le_of_lt (lt_of_not_ge fun hdc ↦ hc (hd.mono hdc)))
  exact absurd h (not_le.2 this)

/-- The bound `cd(f) ≤ d` for a morphism `f : X ⟶ Y`: the higher direct images `Rᵠf_* F`
vanish for every torsion abelian étale sheaf `F` on `X` and every `q > d`. -/
def Hom.HasTorsionCohomologicalDimensionLE {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
    ∀ q : ℕ, d < q → IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)

/-- The torsion étale cohomological dimension `cd(f) ∈ ℕ∞` of a morphism `f : X ⟶ Y`, the least
`d` such that `Rᵠf_* F = 0` for every torsion abelian étale sheaf `F` on `X` and every `q > d`
(and `⊤` if there is none). -/
noncomputable def Hom.torsionCohomologicalDimension {X Y : Scheme.{u}} (f : X ⟶ Y) : ℕ∞ :=
  ⨅ (d : ℕ) (_ : f.HasTorsionCohomologicalDimensionLE d), (d : ℕ∞)

end AlgebraicGeometry.Scheme
