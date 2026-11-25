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
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseScalarFiberMaps
import all WeilConjectures.AlgebraicGeometry.GaloisCategories
import all WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import all WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.RepresentationTheory.Rep.Basic
import all WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import all WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
import all Mathlib.CategoryTheory.Conj
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import all WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
/-! # The canonical continuous integral Galois fibre functor

Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9.
(blueprint: new-e7-canonical-integral-galois-functor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite Topology
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  (c : GaloisLisseFiniteCorrespondence y G)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)

end AlgebraicGeometry.Scheme
