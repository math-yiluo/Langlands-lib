/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Torsion abelian étale sheaves

A sheaf of abelian groups is torsion (`CategoryTheory.Sheaf.IsTorsion`) if every section is
locally torsion, equivalently if every geometric stalk is a torsion group.

## Main statements

- `AlgebraicGeometry.Scheme.isTorsion_of_nsmul_id_eq_zero`: a sheaf killed by `N > 0` is
  torsion.
- `AlgebraicGeometry.Etale.isTorsion_upperStar`: the pullback of a torsion étale sheaf along any
  morphism of schemes is torsion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open scoped Etale

/-- An abelian étale sheaf all of whose sections are killed by `N > 0` is torsion. -/
lemma Scheme.isTorsion_of_nsmul_id_eq_zero {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {N : ℕ} (hN : 0 < N)
    (h : N • 𝟙 F = 0) : F.IsTorsion := by
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U s ↦ ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, ?_⟩
  have h₂ := congrArg (fun φ ↦ ((sheafToPresheaf _ _).map φ).app U) h
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h₂
  simpa using congrArg (fun g ↦ g.hom s) h₂

/-- The pullback `g^* F` of a torsion étale sheaf `F` along a morphism of schemes `g` is torsion:
torsion is checked on geometric stalks
(`AlgebraicGeometry.Scheme.isTorsion_iff_isAddTorsion_sheafFiber`), and the stalk of `g^* F` at
a geometric point `s` is the stalk of `F` at `s ≫ g`
(`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`). -/
theorem Etale.isTorsion_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : F.IsTorsion) :
    ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F).IsTorsion := by
  rw [Scheme.isTorsion_iff_isAddTorsion_sheafFiber] at hF ⊢
  intro Ω _ _ s
  let e := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g s).app F
  exact IsAddTorsion.of_surjective (f := e.inv.hom) (ConcreteCategory.bijective_of_isIso e.inv).2
    (hF Ω (s ≫ g))

end AlgebraicGeometry
