/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-! # Quasi-coherent algebras and their affine-local properties

Source: Stacks Project, Properties, Section 28.23, Tags 05JS, 05JT, 086N and 0817
(blueprint: def-weil-pbc-quasi-coherent-algebra).

Algebra sheaves and their underlying modules reuse `Scheme.CommAlgebraSheaf`
and `Scheme.CommAlgebraSheaf.toModule`. Quasi-coherence uses Mathlib's existing
module-sheaf predicate. Finiteness, integrality and finite presentation are tested
on every affine open using the existing ring-homomorphism predicates.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry

/-- Quasi-coherence of the existing underlying module of an algebra sheaf.
Source: Stacks, Properties, Section 28.23
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def Scheme.IsQuasiCoherentAlgebra (X : Scheme.{u}) : ObjectProperty X.CommAlgebraSheaf :=
  fun A ↦ A.toModule.IsQuasicoherent

/-- The full category of quasi-coherent algebra sheaves.
Source: Stacks, Properties, Section 28.23
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
abbrev QuasiCoherentAlgebra (X : Scheme.{u}) := (X.IsQuasiCoherentAlgebra).FullSubcategory

/-- A finite algebra sheaf has finite section algebras on every affine open.
Source: Stacks, Properties, definitions before Tag 086N
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def Scheme.CommAlgebraSheaf.IsFinite {X : Scheme.{u}} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.Finite

/-- An integral algebra sheaf has integral section algebras on every affine open.
Source: Stacks, Properties, definitions before Tag 086N
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def Scheme.CommAlgebraSheaf.IsIntegral {X : Scheme.{u}} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.IsIntegral

/-- Finite presentation as an algebra, rather than as a module, on every affine open.
Source: Stacks, Properties, definition before Tag 05JS
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def Scheme.CommAlgebraSheaf.IsFinitePresentation {X : Scheme.{u}}
    (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.FinitePresentation

/-- The ordered collection of all finite quasi-coherent subalgebras of `A`.
Subobjects of algebra sheaves identify inclusions that differ by an isomorphism.
Source: Stacks, Properties, Tag 0817(1)
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
abbrev QuasiCoherentAlgebra.FiniteSubalgebras {X : Scheme.{u}}
    (A : QuasiCoherentAlgebra X) :=
  {B : Subobject A.obj // X.IsQuasiCoherentAlgebra (B : X.CommAlgebraSheaf) ∧
    Scheme.CommAlgebraSheaf.IsFinite (B : X.CommAlgebraSheaf)}

/-- The diagram of finite quasi-coherent subalgebras, with their inclusion maps.
Source: Stacks, Properties, Tag 0817(1)
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def QuasiCoherentAlgebra.finiteSubalgebraDiagram {X : Scheme.{u}}
    (A : QuasiCoherentAlgebra X) : A.FiniteSubalgebras ⥤ X.CommAlgebraSheaf :=
  (show Monotone (fun B : A.FiniteSubalgebras ↦ B.val) from
    fun _ _ h ↦ h).functor ⋙ Subobject.underlying

end AlgebraicGeometry
