/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
public import WeilConjectures.AlgebraicGeometry.Sites.TypePointFunctions
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constancy of sheaves of modules on a connected scheme

On a connected scheme, a sheaf of `Λ`-modules on the small étale site is constant as soon as its
underlying sheaf of sets is: both constant sheaf functors are fully faithful there.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- **On a connected scheme, constancy of a sheaf of modules can be tested on sets.** -/
theorem isConstant_of_isConstant_sheafCompose_forget {X : Scheme.{u}} [ConnectedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F).IsConstant
      X.smallEtaleTopology] :
    F.IsConstant X.smallEtaleTopology :=
  Sheaf.isConstant_of_forget _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) F
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)

end AlgebraicGeometry.Scheme
