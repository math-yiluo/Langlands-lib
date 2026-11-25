/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.RingTheory.Depth

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.Finiteness
import WeilConjectures.RingTheory.DepthOneOfMaximalNotAssociated
import WeilConjectures.AlgebraicGeometry.Morphisms.BoundaryMaximalNotAssociated

/-! # Positive depth of finite boundary submodules

## References

* Stacks Project, Tags 0AV8, 0AVN, 0E9I, 01LC, 05AM and 00LL
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Positive depth of finite boundary submodules. -/
theorem depth_one_affine_boundary_submodule
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG)
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hy : hV.fromSpec ⟨p, inferInstance⟩ ∉ U) :
    ∃ hfinite : Module.Finite (Localization.AtPrime p) (LocalizedModule.AtPrime p S),
      letI := hfinite
      (1 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
        (LocalizedModule.AtPrime p S) := by
  classical
  let R := L.presheaf.obj (op V)
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite R S := Module.Finite.of_fg hS
  have hfinite : Module.Finite (Localization.AtPrime p)
      (LocalizedModule.AtPrime p S) := inferInstance
  refine ⟨hfinite, ?_⟩
  exact depth_one_of_finite_localized_module_of_no_maximal_associated
    (boundary_maximal_not_associated U N hqc V hV S hS p hy)

end AlgebraicGeometry.Scheme
