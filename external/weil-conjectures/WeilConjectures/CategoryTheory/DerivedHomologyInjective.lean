/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective

@[expose] public section

universe w uA vA

open CategoryTheory

namespace CategoryTheory

/-- Zeroth cohomology computes maps from any derived object into an injective
object concentrated in degree zero.

Source: the injective comparison in proof step 1 of
`new-stage3-derived-large-coproducts-transfer`.

Proof in words: represent K by a complex C. The single complex I[0] is K-injective,
so maps in the derived category are chain maps C -> I[0] modulo homotopy.
A chain map is a map C⁰ -> I killing the degree-minus-one boundaries. It restricts
on degree-zero cycles to a map H⁰(C) -> I. Conversely, lift a map H⁰(C) -> I
along cycles modulo boundaries into C⁰ modulo boundaries by injectivity of I.
This gives a chain map inducing the specified cohomology map. If a chain map
induces zero, its degree-zero component factors through C⁰/Z⁰(C), the image of
C⁰ -> C¹. Extend the resulting map from that image to C¹ by injectivity of I;
this extension is a null homotopy. Thus the cohomology map is both surjective
and injective. Transport along the canonical localization and single-object
cohomology isomorphisms. This argument also covers acyclic C and the zero
injective, and does not require any coproduct in either category.

(auxiliary; not a blueprint node) -/
theorem derived_homology_injective_bijective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (I : A) [Injective I] :
    Function.Bijective
      ((DerivedCategory.homologyFunctor A 0).map :
        (K ⟶ (DerivedCategory.singleFunctor A 0).obj I) →
      ((DerivedCategory.homologyFunctor A 0).obj K ⟶
          (DerivedCategory.homologyFunctor A 0).obj
            ((DerivedCategory.singleFunctor A 0).obj I))) := by
  constructor
  · exact derived_homology_injective_injective K I
  · exact derived_homology_injective_surjective K I

end CategoryTheory
