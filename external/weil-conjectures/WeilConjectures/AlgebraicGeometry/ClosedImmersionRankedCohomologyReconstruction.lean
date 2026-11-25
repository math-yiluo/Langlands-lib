/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionAlgebraDirectImageExact
import WeilConjectures.AlgebraicGeometry.ClopenRankStrataFormality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Reconstruction from cohomology on finitely many rank strata

Source: the rank-stratum assembly step of
lem-sc-koszul-regular-immersion-algebra-dual, following Stacks Tags 0BQZ and 0AVW.
-/

@[expose] public section

universe u wZ wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Over the algebra of a closed immersion, rank-stratified cohomology determines
its derived object. M is arbitrary: this is the assembly step, independent of any
Koszul resolution, regularity, normal bundle, or scalar right adjoint.

Source: Stacks Project, Tag 0BQZ (single-degree reconstruction) and Tag 0AVW
(algebra-valued direct image); the parent node's proof, step 3
(blueprint: lem-sc-closed-immersion-ranked-cohomology-reconstruction).

Proof:
1. For a closed embedding, direct image of sheaves is exact: at a point of Z its
   stalk is the original stalk, and outside Z it is zero. The identity ring map
   in g = toDirectImageAlgebraSpace i makes this an exact functor of modules.
   Consequently Rg_* is computed by termwise g_* on every complex, without a
   quasi-coherence or boundedness hypothesis. The zero-differential exterior
   complex has homology equal to locallyRankedExteriorTerm in each degree.
2. The clopen fibers of r cover Z. The finite-image hypothesis makes this a finite
   partition. Glue one on a fiber and zero on its complement to obtain sections
   e_n of OZ. Their images in i_* OZ are mutually orthogonal idempotents whose
   sum is one. Multiplication by them splits every algebra-module complex
   termwise, compatibly with its differentials and quasi-isomorphisms.
3. Apply this splitting to a representative of K. By hK, its e_n summand has zero
   cohomology outside degree n, and in degree n has the e_n summand of g_* of
   the stated exterior term. Canonical truncation above and below n gives a
   zigzag of quasi-isomorphisms to that module placed in degree n. In the derived
   category this is the single-degree reconstruction furnished by the standard
   t-structure. Apply the same truncation to the corresponding summand of the
   termwise pushed-forward exterior complex and use the cohomology isomorphism.
4. Take the finite direct sum of the summand isomorphisms and use the splitting
   isomorphisms of step 2. Step 1 identifies the exterior side with Rg_* of its
   localization, with independent chosen derived-category universes.
For empty Z the algebra is zero and every complex is zero. Rank zero gives a
single degree-zero summand. Different ranks are split by the algebra idempotents;
their images are not assumed open or clopen in Y. -/
theorem closedImmersion_rankedCohomology_reconstruction
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (M : Z.Modules) (r : LocallyConstant Z ℕ) (hfinite : (Set.range r).Finite)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
          (Scheme.Modules.locallyRankedExteriorTerm M r n))) :
    Nonempty ((RingedSpace.derivedModuleDirectImage
      (toDirectImageAlgebraSpace i)).obj (DerivedCategory.Q.obj
        (Scheme.Modules.locallyRankedExteriorComplex M r)) ≅ K) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)
  let : PreservesFiniteLimits F := by
    unfold F RingedSpace.moduleDirectImage
    infer_instance
  let : PreservesFiniteColimits F :=
    closedImmersion_algebraDirectImage_preservesFiniteColimits i
  let C := Scheme.Modules.locallyRankedExteriorComplex M r
  let e : (RingedSpace.derivedModuleDirectImage
      (toDirectImageAlgebraSpace i)).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
    F.rightDerivedFunctorIsoMapDerivedCategory.app (DerivedCategory.Q.obj C) ≪≫
      F.mapDerivedCategoryFactors.app C
  let E (n : ℕ) := Scheme.Modules.exteriorPower
    ((Scheme.Modules.restrictFunctor (Scheme.Modules.exteriorRankOpen r n).ι).obj M) n
  obtain ⟨eK⟩ := clopenRankStrata_formality i r hfinite E
    (Scheme.Modules.locallyRankedExteriorTerm M r) (fun _ => rfl) K hK
  exact ⟨e ≪≫ eK⟩

end AlgebraicGeometry
