/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver

/-! # The dual of a module of constant finite rank

The ordinary dual `Hom(M, O)` of a finite locally free module of constant rank `r` is again
finite locally free of rank `r`: on each trivializing open, `Hom(O^r, O) ≅ O^r`.

## References

* Stacks Project, Tag 01C6
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The dual of a finite locally free module of constant rank `r` has constant rank `r`. -/
instance isFiniteLocallyFreeOfRank_dual {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] : (dual M).IsFiniteLocallyFreeOfRank r := by
  obtain ⟨q, hq, hr⟩ :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.exists_localGeneratorsData (M := M) (r := r)
  refine SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.mpr
    ⟨q.I, q.X, q.coversTop, fun i ↦ ⟨?_⟩⟩
  have := hq.isIso i
  let e : M.over (q.X i) ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
    (asIso (q.generators i).π).symm ≪≫ SheafOfModules.freeFunctor.mapIso
      ((hr i).some.trans Equiv.ulift.symm).toIso
  exact SheafOfModules.overHomObjIso M (SheafOfModules.unit X.ringCatSheaf) (q.X i) ≪≫
    ((SheafOfModules.homFunctor (X.sheaf.over (q.X i))).flip.obj
      (SheafOfModules.unit _)).mapIso e.symm.op ≪≫ SheafOfModules.homObjFreeUnitIso.{u} _

end AlgebraicGeometry.Scheme.Modules
