/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport

/-! # The fixed module/Ext comparison respects h-maps

## References

* Stacks Project, Tag 01FB (coefficient factorization) and Tag 03FD (comparison)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The resolution comparison respects h-maps in its original Ext universe. -/
theorem moduleCohomologyExtResolutionEquiv_hmap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (pushforward g).obj G)
    (q : ℕ) (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleCohomologyExtResolutionEquiv Y G q (moduleCohomologyFMap g φ q x) =
      Sheaf.H.map (coeff g φ) q
        (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q
          (moduleCohomologyExtResolutionEquiv X F q x)) := by
  exact moduleCohomology_transport_coefficient g F G φ q
    (fun M ↦ moduleCohomologyExtResolutionEquiv X M q)
    (moduleCohomologyExtResolutionEquiv Y G q)
    (moduleCohomologyExtResolutionEquiv_naturality X q F _ φ)
    (moduleCohomologyExtResolutionEquiv_edge g G q) x

end
end AlgebraicGeometry.Scheme.Modules
