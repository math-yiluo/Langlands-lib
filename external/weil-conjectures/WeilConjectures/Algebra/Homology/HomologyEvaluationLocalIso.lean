/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpen
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomologyEvaluationLocalIsoCore

/-! # A step in the construction of homology evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Evaluation is locally an isomorphism under the finite-free model hypotheses.
Source: Stacks Project, Tag 0BQY, zero-differential Hom calculation.
(blueprint: new-b2-homology-evaluation-local-iso).

Proof: Termwise open restriction is exact and commutes with the Hom complex,
internal Hom, cycles and homology. Hence the restricted cycle formula describes
the evaluation map for F(T), F(J), and F(J) still has no homology outside zero.
Choose the specified roof L -> F(T), L -> E. Since F(J) is K-injective, applying
Hom(-,F(J)) to either arrow gives a quasi-isomorphism. The product-component
naturality formula makes cycle evaluation commute with both precomposition
maps; on homology this is a commutative square whose horizontal comparison maps
are isomorphisms. Internal Hom of the induced homology isomorphisms also gives
isomorphisms. Thus invertibility of evaluation can be checked on E.
For E with zero differential, group the finitely many nonzero factors of Hom(E,F(J))
by their source degree p. Its differential on each factor is the differential
of Hom(E^p,F(J)), shifted by -p. A finite-free E^p of rank r makes this factor
the finite product of r copies of F(J). Finite products in modules are exact,
so its homology is Hom(E^p,H^(p+n)(F(J))). Concentration in degree zero removes
all factors except p=-n. Since E has zero differential, H^(-n)(E)=E^(-n).
Under these identifications evaluation is the identity on
Hom(E^(-n),H^0(F(J))), so it is invertible. Transport around the two squares
proves the conclusion for F(T). If -n is outside the support, both sides are
zero; rank zero, zero rings and empty opens obey the identical calculation. -/
theorem homologyEvaluation_local_iso_of_cycle (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (hT : HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W)
      ((moduleOpenOverComplexFunctor X V W).obj T)) :
    IsIso (((Scheme.Modules.restrictFunctor V.ι).map e).over W) := by
  obtain ⟨E, L, q, p, hq, hp, hzero, hsupp, hfree⟩ := hT
  exact homologyEvaluation_local_iso_of_roof X T J n hJ e he V W hI E L q p hq hp
    hzero hsupp hfree

end CategoryTheory
