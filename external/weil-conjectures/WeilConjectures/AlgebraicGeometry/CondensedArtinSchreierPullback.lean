/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Pullback of the condensed Artin--Schreier sheaf of a function

Source: latest blueprint, lem-fd-base-change.proof.md, integrand paragraph.
(blueprint: lem-fd-condensed-artin-schreier-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] condensedArtinSchreierSheaf

-- Keep the exact derived comparison generic before instantiating the character image.
private theorem nonempty_derivedPullback_single_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ Z) (q' : X ⟶ Z) (hq : f ≫ q = q')
    (A : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    Nonempty ((CondensedRing.upperStar Λ f).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.upperStar Λ q).obj A)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Λ q').obj A)) := by
  exact ⟨(CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).app _ ≪≫
    ((CondensedRing.upperStar Λ f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((CondensedRing.upperStarComp Λ f q).symm.app A ≪≫
        eqToIso (congrArg (fun t ↦ (CondensedRing.upperStar Λ t).obj A) hq))⟩

-- Keep the character image abstract during the derived comparisons.
/-- The degree-zero Artin--Schreier complex pulls back to the complex of the
pulled-back function, including on the empty scheme.

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/
lem-fd-base-change.proof.md, integrand paragraph
(blueprint: lem-fd-condensed-artin-schreier-pullback).

Proof: Module pullback is exact, so its derived functor agrees with the termwise
functor and carries a degree-zero complex to the degree-zero pullback. The map
to affine one-space defined by the pulled-back function is the composite of the
original map with the scheme morphism, by the coordinate description of
homOfVector. The module pullback composition isomorphism therefore identifies
the two degree-zero modules. No flatness or nontriviality of the character is
needed, since the coefficient ring is pulled back from the point. -/
theorem nonempty_iso_condensedArtinSchreierSheafOf_derivedPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (ψ : AddChar k (MonObj.Γ Λ)) (b : Γ(Y, ⊤)) :
    Nonempty ((CondensedRing.upperStar Λ f).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (condensedArtinSchreierSheafOf Λ k Y ψ b)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (condensedArtinSchreierSheafOf Λ k X ψ (f.appTop b))) := by
  let q := AffineSpace.homOfVector (Y ↘ Spec (.of k)) (fun _ : PUnit ↦ b)
  have hq : f ≫ q =
      AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit ↦ f.appTop b) := by
    dsimp only [q]
    rw [AffineSpace.comp_homOfVector, CategoryTheory.comp_over]
    rfl
  exact nonempty_derivedPullback_single_comp Λ f q _ hq
    (condensedArtinSchreierSheaf Λ k ψ)

end AlgebraicGeometry.ProEtale
