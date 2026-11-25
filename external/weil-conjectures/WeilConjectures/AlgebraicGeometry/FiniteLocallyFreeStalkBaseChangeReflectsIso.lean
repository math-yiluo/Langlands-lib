/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.StalkFiniteFree
import WeilConjectures.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso

/-! # Reflection of invertibility at a vector bundle stalk

Source: Stacks Project, Tag 00O0, Lemma 10.79.4(3), finite free matrix argument.
(blueprint: lem-sc-finite-locally-free-stalk-base-change-reflects-iso)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Extension along the local ring map of a scheme morphism reflects invertibility
of a map between finite locally free stalks.
Source: Stacks Project, Tag 00O0, Lemma 10.79.4(3), finite free matrix argument.
(blueprint: lem-sc-finite-locally-free-stalk-base-change-reflects-iso)

Proof: Choose finite free frames for M and N near h(t), so their stalks are free
of finite ranks m and n over R = O_{W,h(t)}. Put S = O_{T,t}. Reducing the given
isomorphism over S modulo its maximal ideal gives an isomorphism over k(t).
The local map R to S induces a field extension k(h(t)) to k(t). A matrix over a
field is injective or surjective if and only if its scalar extension to a larger
field is, as can be checked by ranks or Gaussian elimination. Thus m = n and
the determinant of the original matrix is nonzero modulo the maximal ideal of R.
An element of a local ring with nonzero residue is a unit. The adjugate divided
by this unit is a two-sided inverse of the stalk matrix. Transporting back along
the chosen frames gives the stated stalk isomorphism. For m = n = 0 the map
between zero modules is invertible; for unequal ranks the premise is impossible.
No flatness of R to S is used. -/
theorem isIso_moduleStalkMap_of_isIso_extendScalars
    {W T : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    (h : T ⟶ W) (t : T)
    (hφ : IsIso ((ModuleCat.extendScalars (h.stalkMap t).hom).map
      ((RingedSpace.moduleStalkFunctor W.toRingedSpace (h t)).map φ))) :
    IsIso ((RingedSpace.moduleStalkFunctor W.toRingedSpace (h t)).map φ) := by
  let R := W.presheaf.stalk (h t)
  let S := T.presheaf.stalk t
  let f : R →+* S := (h.stalkMap t).hom
  have hM := stalk_isFiniteFree_of_isFiniteLocallyFree M (h t)
  have hN := stalk_isFiniteFree_of_isFiniteLocallyFree N (h t)
  have := hM.1
  have := hM.2
  have := hN.1
  have := hN.2
  exact isIso_of_isIso_extendScalars_of_finite_free f
    ((RingedSpace.moduleStalkFunctor W.toRingedSpace (h t)).map φ) hφ

end AlgebraicGeometry.Scheme.Modules
