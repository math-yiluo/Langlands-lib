/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import WeilConjectures.AlgebraicGeometry.Modules.DualRetractionKey

/-!
# Local retractions of transposes from local sections

## References

* [Stacks: Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- If `f : P ⟶ Q` has a section over the open `U`, then the restriction of its transpose
`Qᵛ ⟶ Pᵛ` to `U` is a split monomorphism. -/
theorem isSplitMono_restrict_dualMap_of_local_section
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) (U : X.Opens)
    (s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P)
    (hs : s ≫ (restrictFunctor U.ι).map f = 𝟙 _) :
    IsSplitMono ((restrictFunctor U.ι).map (dualMap f))  := by
  let F := restrictFunctor U.ι
  obtain ⟨e, he⟩ := internalHom_restrict_scheme U
  let r : F.obj (dual P) ⟶ F.obj (dual Q) :=
    (e P (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf) s (𝟙 _) ≫
      (e Q (SheafOfModules.unit X.ringCatSheaf)).inv
  refine IsSplitMono.mk ⟨⟨r, ?_⟩⟩
  exact dual_retraction_key f U s e he hs

end AlgebraicGeometry.Scheme.Modules
