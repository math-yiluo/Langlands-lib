/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalGlobalSectionsExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyIso
import Mathlib.Algebra.Category.Grp.Zero

/-! # Zero-dimensional étale cohomology: cohomological remainder

Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-arbitrary-curve-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, both proof paragraphs.
(blueprint: zero-dimensional-etale-cohomology-rest).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Positive étale cohomology is zero, and the canonical degree-zero comparison
followed by the product of the chosen geometric stalk germs is invertible.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-arbitrary-curve-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, both proof paragraphs;
Stacks Project, Tags 00KH, 00FV, 054M, 03QT, 03QU, 03SI and 03Q1.
(blueprint: zero-dimensional-etale-cohomology-rest).

Proof: Apply `zero_dimensional_global_sections_preservesFiniteColimits`; global
sections already preserve finite limits. The exact-functor comparison
`Functor.singleFunctorCompRightDerivedFunctorIso` identifies derived global
sections of F in degree zero with ordinary global sections placed in degree zero.
Transport the vanishing of the homology of a single complex in positive degree
through this comparison, then use `AddCommGrpCat.subsingleton_of_isZero`.
The degree-zero conjunct is `zero_dimensional_etale_cohomology_iso`, which keeps
the reduction, finite coproduct, and canonical germ compatibility route described
in the source. Neither unresolved obligation restates this conjunction.
-/
theorem zero_dimensional_etale_cohomology_rest
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    (∀ q : ℕ, 0 < q → Subsingleton
      ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsIso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫ Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  have : PreservesFiniteColimits (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    zero_dimensional_global_sections_preservesFiniteColimits k C f hdim
  refine ⟨fun q hq => AddCommGrpCat.subsingleton_of_isZero ?_,
    zero_dimensional_etale_cohomology_iso k C f hdim F Ω s hs⟩
  change IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
    ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F)))
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
    ((Functor.singleFunctorCompRightDerivedFunctorIso
      (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).app F))
  change IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
    ((DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} 0).obj
      ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F)))
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
    ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F)
    (q : ℤ) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ AddCommGrpCat.{u + 1} 0).app
        ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F)) ≪≫
      (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _)

end AlgebraicGeometry
