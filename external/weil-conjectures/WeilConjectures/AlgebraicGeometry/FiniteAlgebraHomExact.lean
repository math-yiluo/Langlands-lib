/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
import WeilConjectures.AlgebraicGeometry.ExtEvaluation
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule

/-! # Exactness of the algebra-valued finite sheaf-Hom functor
Source: Stacks Project, Tags 0BUZ and 01C6
(blueprint: lem-sc-finite-algebra-hom-exact). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry

/-- The algebra-valued Hom functor is exact when its first argument is finite locally free.
Source: Stacks Project, Duality for Schemes, Tag 0BUZ; Modules, Tag 01C6
(blueprint: lem-sc-finite-algebra-hom-exact).

Proof: The dual of A is finite locally free. Canonical evaluation identifies tensoring
by that dual with Hom(A,-), naturally in the coefficient module, by
`dual_tensor_hom_iso`. Tensoring by the dual preserves finite limits and colimits by
`finiteLocallyFree_tensorLeft_exact`. Restriction of scalars preserves and reflects
kernels and cokernels: their underlying sheaves and maps are unchanged. Transport
exactness through iH and reflect it to H. This includes rank zero and empty schemes. -/
theorem finite_algebraHom_exact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))]
    (H : Y.Modules ⥤ SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    (iH : H ⋙ SheafOfModules.restrictScalars f.toRingCatSheafHom ≅
      (SheafOfModules.homFunctor Y.sheaf).obj
        (op ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))))
    : PreservesFiniteLimits H ∧ PreservesFiniteColimits H := by
  let A := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  have := Scheme.Modules.IsFiniteLocallyFree.dual A
  obtain ⟨hlim, hcolim⟩ := Scheme.Modules.finiteLocallyFree_tensorLeft_exact
    (Scheme.Modules.dual A)
  let := hlim
  let := hcolim
  obtain ⟨e, _, he⟩ := Scheme.Modules.dual_tensor_hom_iso Y A
  let i : tensorLeft (Scheme.Modules.dual A) ≅
      (SheafOfModules.homFunctor Y.sheaf).obj (op A) :=
    NatIso.ofComponents e (fun g ↦ (he g).symm)
  let T := SheafOfModules.restrictScalars f.toRingCatSheafHom
  have : PreservesFiniteLimits (H ⋙ T) :=
    preservesFiniteLimits_of_natIso (i ≪≫ iH.symm)
  have : PreservesFiniteColimits (H ⋙ T) :=
    preservesFiniteColimits_of_natIso (i ≪≫ iH.symm)
  have : T.ReflectsIsomorphisms := by
    constructor
    intro N P g hg
    have := hg
    have h : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map (T.map g)) :=
      inferInstance
    have : IsIso ((SheafOfModules.toSheaf
      (moduleRings (directImageAlgebraSpace f))).map g) := h
    exact isIso_of_reflects_iso g
      (SheafOfModules.toSheaf.{u} (moduleRings (directImageAlgebraSpace f)))
  have : PreservesFiniteLimits T :=
    @sheafAlgebraRestrictScalars_preservesFiniteLimits.{u, _, _} Y
      (Under.mk (show Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf from ⟨f.c⟩))
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
  have : PreservesFiniteColimits T :=
    @sheafAlgebraRestrictScalars_preservesFiniteColimits.{u, _, _} Y
      (Under.mk (show Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf from ⟨f.c⟩))
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
  have : ReflectsFiniteLimits T :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves H T,
    preservesFiniteColimits_of_reflects_of_preserves H T⟩

end AlgebraicGeometry
