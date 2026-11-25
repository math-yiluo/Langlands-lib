/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.Algebra.Homology.ExtInjectiveResolutionComparison
import WeilConjectures.Algebra.Homology.FilteredColimitCochainHomology
import WeilConjectures.Algebra.Homology.QuotientHomComplexColimit

/-! # Ext-colimit local cohomology and derived ideal-power torsion

Source: Stacks Project, Tag 0954, Lemma 47.8.2.
-/

@[expose] public section

universe u
open CategoryTheory

namespace ModuleCat

/-- The Ext-colimit computes the right derived functors of ideal-power torsion.
Source: Stacks Project, Tag 0954, Lemma 47.8.2.
(blueprint: lem-sbc-local-cohomology-derived-torsion).

Proof: Choose an injective resolution M → E. For each n, compute Mathlib's
projectively defined Ext by a projective resolution P of R/J^n. The first-quadrant
double complex Hom(P,E) compares Hom(P,M) with Hom(R/J^n,E): exactness of
Hom(P^i,-) and Hom(-,E^j) makes both augmentations cohomology isomorphisms.
Projective comparison maps lifting the quotient transitions, unique up to homotopy,
show that these identifications are compatible with the directed system.
Thus Ext^q(R/J^n,M) is naturally H^q(Hom(R/J^n,E)). Evaluation at 1 identifies
Hom(R/J^n,E^k) with
the submodule of E^k annihilated by J^n. The transition induced by
R/J^(n+1) → R/J^n is the inclusion of these submodules, so their filtered
colimit is precisely Ideal.primaryComponent E^k J. These identifications
commute with the differential induced by E. Filtered colimits of modules
are exact and therefore commute with cohomology. Thus the colimit of the
Ext groups is the cohomology of the torsion subcomplex of E, which computes
the displayed right derived functor. The exponent zero contributes the zero
submodule and does not affect the colimit. This works also for J=0 and J=R,
when the torsion functor is respectively the identity and zero. -/
theorem nonempty_localCohomology_iso_derived_torsion
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J.FG)
    (M : ModuleCat.{u} R) (q : ℕ) :
    Nonempty ((localCohomology J q).obj M ≅
      ((idealPowerTorsion J).rightDerived q).obj M) := by
  have _hJ := hJ
  clear _hJ hJ
  let E := injectiveResolution M
  let Q := (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J)).op
  let F := Q ⋙ homComplexDiagram E.cocomplex
  obtain ⟨e⟩ := nonempty_ext_iso_injectiveResolution_homology M E q
  obtain ⟨h⟩ := nonempty_colimit_homology_iso F q
  obtain ⟨t⟩ := nonempty_colimit_quotientHomComplex_iso_torsion J E.cocomplex
  let c := CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation
    (localCohomology.diagram (localCohomology.idealPowersDiagram J) q) M
  refine ⟨c ≪≫ ?_ ≪≫ h ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).mapIso t ≪≫
      (E.isoRightDerivedObj (idealPowerTorsion J) q).symm⟩
  exact CategoryTheory.Limits.HasColimit.isoOfNatIso (Functor.isoWhiskerLeft Q e)

end ModuleCat
