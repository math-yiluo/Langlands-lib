/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.AlgebraicGeometry.SheafAlgebraMapDerivedAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The constructed algebra-valued derived Hom adjunction

Source: Stacks Project, Duality for Schemes, Tags 0BV0 and 0BV1, with Modules Tag 0A6F
and Derived Categories Tag 09T5
(blueprint: lem-sc-sheaf-algebra-derived-hom-adjunction).
-/

@[expose] public section

universe u w wB

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry

/-- The explicit algebra-valued derived Hom is right adjoint to derived restriction
of scalars. No finiteness, Noetherianity, cohomological bound, or assertion about
quasi-coherence of the output is involved.
Source: Stacks Project, Duality for Schemes, Tags 0BV0 and 0BV1, with Modules Tag 0A6F
and Derived Categories Tag 09T5
(blueprint: lem-sc-sheaf-algebra-derived-hom-adjunction).

Proof:
1. Restriction along B.hom has right adjoint sheafAlgebraHom Y B. On an open U,
   an O-linear map from the restricted M to F determines the B-linear map to
   Hom(B,F) by m ↦ (b ↦ φ(bm)); evaluation at 1 is its inverse. These formulas
   commute with restriction and postcomposition and give the sheaf adjunction.
2. Restriction of scalars is exact: its finite-limit and finite-colimit properties
   are sheafAlgebraRestrictScalars_preservesFiniteLimits and
   sheafAlgebraRestrictScalars_preservesFiniteColimits. Consequently its derived
   functor is its termwise localization mapDerivedCategory.
3. Compute the right derived Hom on the fixed functorial K-injective resolution
   sheafAlgebraHomResolution. The underived right adjoint sends K-injectives to
   K-injectives because its exact left adjoint preserves acyclic complexes.
   Thus the derived adjunction exists and its right functor is the localization
   of Hom(B,I(-)). The comparison derivedRHomAlgebraModule_comparison identifies
   this with the explicitly constructed derivedRHomAlgebraModule, including the
   B-action, since both use sheafAlgebraHom and the same resolution.
4. Localization uniqueness and the exact-functor comparison with
   rightDerivedFunctor transport the adjunction to the stated left functor.
   Evaluation at one and multiplication still give inverse maps when B is zero,
   when Y is empty, and for unbounded complexes; the K-injective argument applies
   in all these cases. -/
theorem sheafAlgebraDerivedHom_adjunction
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).rightDerivedFunctor ⊣
          derivedRHomAlgebraModule Y B hB) := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).map B.hom)
  have : PreservesFiniteLimits F := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits F := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  obtain ⟨adj⟩ := sheafAlgebra_mapDerivedCategory_adjunction Y B hB
  exact ⟨adj.ofNatIsoLeft F.rightDerivedFunctorIsoMapDerivedCategory.symm⟩

end AlgebraicGeometry
