/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Dualizability of a lisse flat sheaf in degree zero

## References

* Bhatt--Scholze, *Pro-étale topology*, Section 6.4, printed pp. 48--49
* Bhatt--Scholze, Pro-étale topology, Example 6.4.1 and Lemma 6.4.6
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

attribute [local instance] Sheaf.monoidalCategory

namespace AlgebraicGeometry.Etale

/-- A finite locally constant module sheaf with flat geometric stalks is dualizable
when placed in degree zero in the ordinary unbounded étale derived category. -/
theorem isDualizable_singleFunctor_lisseFlat
    {C : Type (u + 1)} [CommRing C] [Finite C]
    {V : Scheme.{u}} (L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C))
    [Scheme.IsFiniteLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ V),
      ObjectProperty.flat ((Scheme.pointSmallEtale s).sheafFiber.obj L)) :
    IsDualizable ((DerivedCategory.singleFunctor
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).obj L) := by
  have hflat : ObjectProperty.flat L :=
    (flat_iff_forall_flat_sheafFiber_obj L).2 fun {Ω} _ _ s ↦
      ObjectProperty.prop_of_iso _
        ((Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1}
          (ModuleCat.{u + 1} C) |>.app L).symm (hL Ω s)
  let _ := exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf L hflat
  have hdual : IsDualizable L :=
    ⟨{ rightDual := (ihom L).obj (𝟙_ _)
       exact := BraidedCategory.exactPairing_swap _ _ }⟩
  let P := (HomologicalComplex.single
    (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C)) (.up ℤ) 0).obj L
  have hP : ∀ n, IsDualizable (P.X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact IsDualizable.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).symm hdual
    · exact CategoryTheory.IsZero.isDualizable
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 L n hn)
  have hd : IsDualizable
      ((DerivedCategory.singleFunctor
        (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).obj L) :=
    IsDualizable.of_iso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L).symm
      (DerivedCategory.isDualizable_Q_obj P 0 0 hP)
  exact hd

end AlgebraicGeometry.Etale
