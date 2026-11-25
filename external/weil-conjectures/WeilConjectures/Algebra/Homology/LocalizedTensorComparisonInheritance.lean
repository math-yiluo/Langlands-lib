/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonInheritanceFixedDegree

/-! # Tensor inheritance for localized cohomology comparisons

Source: Stacks Project, perfect.tex, Tag 0DJA(1), local computation using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-inheritance).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModuleCat

/-- Local ring form of tensor inheritance, for actual chain maps and the canonical
scalar-extension tensorator.

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using More on Algebra, Tag 0BYJ.
Proof: write T = A tensor-over-R B. Resolve the R-tensor factor by a K-flat
resolution. The mixed-ring associator identifies the comparison for U tensor Q
with U tensor the comparison for Q, naturally in U and Q and compatibly with the
T-action. Flatness of C over T makes extension to C exact, so its cohomology is
cohomology followed by extension. For fixed Q and t, the complexes U for which
all these cohomology comparisons are invertible form a localizing subcategory
of D(A): shifts reindex the comparisons, sums commute with cohomology and
extension, and triangles give the five lemma in the long exact sequences.
It contains A and all its shifts by the hypothesis. The shifts of A generate
D(A), so it contains every U. K-flatness of U and Q makes the displayed total
complexes compute these derived tensors, and naturality identifies the map
with the inverse scalar-extension tensorator followed by tensoring t.
This applies to arbitrary unbounded complexes and to the zero ring.
(blueprint: lem-pc-localized-tensor-comparison-inheritance). -/
theorem localizedTensorComparison_inheritance
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    (hC : Module.Flat (A ⊗[R] B) C)
    (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} C) ℤ)
    (hU : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} B)
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∀ (t : F.obj Q ⟶ N)
      (m : BaseDerivedTensorCohomologyModel R A B Q C)
      (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C),
      (∀ i : ℤ, IsIso (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i)) →
      ∀ i : ℤ, IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  dsimp
  intro t m mU h i
  exact localizedTensorComparison_inheritance_fixed_degree R A B C hC U Q N hU hQ t m mU i h

end ModuleCat
