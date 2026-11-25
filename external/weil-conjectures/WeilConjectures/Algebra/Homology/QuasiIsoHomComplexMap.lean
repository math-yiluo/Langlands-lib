/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoOfSections

/-!
# Quasi-isomorphisms of sheaf Hom complexes into K-injectives

Source: Stacks Project, sites-cohomology.tex, Lemma 0A95
(sites-cohomology-lemma-RHom-well-defined), using Lemma 0A94
(blueprint: lem-pur-rhom-well-defined).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- The map of sheaf Hom complexes obtained by precomposing with `t` and postcomposing
with `s` is a quasi-isomorphism when `s` and `t` are quasi-isomorphisms and both targets
of the Hom complexes are K-injective.
Source: Stacks Project, sites-cohomology.tex, Lemma 0A95, using Lemma 0A94
(blueprint: lem-pur-rhom-well-defined).

Proof:
1. Fix a site object `U` and an integer `n`. The formula in `def-pur-hom-complex`
   identifies degree `n` cohomology of sections with degree zero cohomology after
   shifting the first complex by `-n`, compatibly with pre- and postcomposition.
   Restriction to the localized site is exact (`lem-weil-pbc-site-restriction-exact`),
   so the restricted `s` and shifted `t` remain quasi-isomorphisms
   (`def-pc-quasi-iso-modules`). Their images under the derived localization functor
   are isomorphisms (`def-weil-abstract-derived-category`). Apply
   `lem-pur-rhom-into-kinjective-local` to both Hom complexes: on degree `n`
   cohomology of sections our map is composition with these two isomorphisms in
   the localized derived category, hence is bijective, naturally in `U`.
2. The cohomology sheaf of a complex (`def-pc-acyclic-complex-modules`) is the
   sheafification of its sectionwise cohomology presheaf: kernels, images and
   quotients are computed sectionwise before applying exact module sheafification
   (`lem-weil-pbc-ringed-site-module-sheafification-exact`). Sheafifying the
   presheaf isomorphisms in Step 1 gives an isomorphism on every cohomology sheaf.
   This is exactly `def-pc-quasi-iso-modules`. -/
theorem quasiIso_homComplex_map
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] :
    QuasiIso (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s) := by
  apply quasiIso_of_sections
  intro U
  exact homComplex_sections_quasiIso s t U

end CategoryTheory
