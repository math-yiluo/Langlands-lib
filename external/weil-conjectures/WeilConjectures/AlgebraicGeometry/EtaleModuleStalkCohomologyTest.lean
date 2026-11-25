/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Module geometric stalks compute and detect unbounded cohomology

Source: Stacks Project, etale-cohomology.tex, Tags 03PT(3) and 03PU;
sites-modules.tex, Tags 03DA and 04EQ; sites-cohomology.tex, Tag 0DJJ;
derived.tex, Tag 015F (blueprint: lem-sf-etale-module-stalk-cohomology-test).

Constant-coefficient modules use the project's module-valued sheaf encoding.
`pointSmallEtale t |>.sheafFiber` is the pointed-neighbourhood colimit, computed
in modules, so its scalar action and maps are the induced A-linear ones.
The derived functor below is the existing exact-functor localization, on the full
unbounded derived categories. All comparisons are natural isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive

namespace AlgebraicGeometry.Etale

/-- Vanishing of each cohomology sheaf is detected by all derived geometric stalks.
Source: Stacks Project, etale-cohomology.tex, Tag 03PU; sites-cohomology.tex,
Tag 0DJJ (blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: steps 1-6 of the node. First forgetting modules preserves kernels,
cokernels, images, quotients and cohomology by
situation-conventions and
lem-sp-exact-functor-preserves-homology. Next the action a[m] = [a_V m] is well
defined on pointed-neighbourhood germs and makes the stalk maps A-linear.
By prop-weil-pbc-geometric-stalks-exact this module stalk is exact. Applying
lem-weil-pbc-exact-functor-complex-cohomology gives the natural cohomology
comparison on unbounded complexes and preservation of quasi-isomorphisms.
By situation-conventions it descends to the full
derived categories, with naturality also for inverses of quasi-isomorphisms.
If the cohomology sheaf is zero, its stalks and hence the corresponding stalk
cohomology modules vanish. Conversely, if those modules vanish, the comparison
makes all abelian stalks of the underlying cohomology sheaf zero. Apply
lemma-weil-pbc-geometric-stalk-conservative to the morphism from zero to that
abelian sheaf. It is an isomorphism, so that sheaf is zero. Faithfulness of the
module forgetful functor then gives id = 0 for the module sheaf, making it zero.
On an empty scheme the condition on geometric points is vacuous, and the same
conservativity argument applies. No boundedness, finiteness, constructibility
or Noetherian hypothesis enters any step. -/
theorem etaleModuleStalk_cohomology_test
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (E : DerivedCategoryModule A T) (i : ℤ) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj E) ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj
          (((pointSmallEtale t).sheafFiber
            (A := ModuleCat.{u + 1} A)).mapDerivedCategory.obj E)) := by
  constructor
  · intro h Ω _ _ t
    let e := ((pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} A)).mapDerivedCategoryHomologyFunctorIso i
    exact (Functor.map_isZero ((pointSmallEtale t).sheafFiber) h).of_iso (e.app E).symm
  · intro h
    apply (IsZero.iff_id_eq_zero _).2
    apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro s
    let e := ((pointSmallEtale (T.algClosurePoint s)).sheafFiber
      (A := ModuleCat.{u + 1} A)).mapDerivedCategoryHomologyFunctorIso i
    have hz := (h _ (T.algClosurePoint s)).of_iso (e.app E)
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hz

end AlgebraicGeometry.Etale
