/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensorCounit

/-! # The monoidal structure of the derived pullback on module objects over `Λ`

The declarations of this module (the tensor counit of a monoidal adjunction, the derived tensor
unit comparison and the strong monoidal structure of the derived pullback) are provided by
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensorCounit`, which this
module re-exports.
-/
