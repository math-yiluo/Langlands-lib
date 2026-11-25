/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.CategoryTheory.Conj
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseIntegralScalarFiberIsomorphism
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
import Mathlib.CategoryTheory.Conj
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction

/-! # The prescribed integral fibre scalar comparison

## References

* Deligne, Weil II (1.1.1) b), d), pp.146-147
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type (u + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber

end AlgebraicGeometry.Scheme
