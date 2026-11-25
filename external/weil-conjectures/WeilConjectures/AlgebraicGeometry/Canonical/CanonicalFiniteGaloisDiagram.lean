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
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction
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

/-! # Canonical finite-level Galois actions on integral stalk towers

Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9.
(blueprint: new-e7-canonical-finite-galois-diagram).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  (c : GaloisLisseFiniteCorrespondence y G)

end AlgebraicGeometry.Scheme
