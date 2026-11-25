/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ModuleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveCechVanishing
import WeilConjectures.AlgebraicGeometry.ModuleSectionsAcyclicOfCohomologyVanishing

/-!
# Direct images of injective modules are acyclic on every open

Source: Stacks Project, Cohomology of Sheaves, Tag 01EX (2), and Tag 01E1 (2)
(blueprint: lem-weil-pbc-module-pushforward-injective-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The direct image of an injective `𝒪_X`-module has zero positive module cohomology
on every open `V` of the target. Equivalently it is acyclic for the module-valued
sections functor `Γ(V,-)`. Direct image need not itself be injective, since tensor
pullback need not be exact.

Source: Stacks Project, Cohomology of Sheaves, Tag 01EX (2), and Tag 01E1 (2)
(blueprint: lem-weil-pbc-module-pushforward-injective-acyclic).

Proof:
1. For any covering `(V_j)` of `V`, inverse images cover `h⁻¹(V)`. Sections of
   `h_* I` on each finite intersection are sections of `I` on its inverse image.
   Inverse image commutes with intersections and the restriction maps agree.
   Thus the Cech complexes coincide, including the alternating differentials
   (lemma-uniform-bounds-pro-etale-affines, def-pc-module-pullback, def-weil-pbc-site-cech-complex).
2. The Cech cohomology of `I` for this covering vanishes in positive degrees by
   lem-weil-pbc-module-injective-open-cover-cech-acyclic (Tag 01EP), so the same
   holds for `h_* I` on every covering of every open.
3. Apply lem-weil-pbc-module-cech-vanishing-criterion (Tag 01EV) to `h_* I` on `S`.
   This gives the first assertion, with module cohomology as in pqf-def-cohomology.
4. Sections over `V` are additive and left exact by sectionwise kernels. Choose an
   injective resolution of `h_* I` using lem-weil-pbc-scheme-modules-enough-injectives
   and def-sp-injective-resolutions. Restrict it to `V`; it remains an injective
   resolution by lem-weil-pbc-module-open-restriction-injectives (Tag 01E1 (2)).
   Sections of the restricted resolution on `V` equal sections of the original
   resolution over `V`, compatibly with the differentials, by
   lem-weil-pbc-module-restriction-open-immersion-colimits. Hence the right derived
   sections functors agree with the cohomology in step 3 and vanish positively.
   This is def-sp-acyclic, and includes the whole space `V = ⊤`. -/
theorem module_pushforward_injective_acyclic {X S : Scheme.{u}} (h : X ⟶ S)
    (I : X.Modules) [Injective I] :
    (∀ (V : S.Opens) (p : ℕ), 0 < p →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace p).obj
        ((restrictFunctor V.ι).obj ((pushforward h).obj I)))) ∧
    (∀ V : S.Opens,
      (SheafOfModules.forget.{u} S.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} S.ringCatSheaf.obj (op V)).rightAcyclic
        ((pushforward h).obj I)) := by
  have hcoh := module_cohomology_isZero_of_cech_vanishing.{u, u} S ((pushforward h).obj I)
    (module_pushforward_injective_cech_vanishing h I)
  exact ⟨hcoh, module_sections_acyclic_of_cohomology_vanishing S _ hcoh⟩

end AlgebraicGeometry.Scheme.Modules
