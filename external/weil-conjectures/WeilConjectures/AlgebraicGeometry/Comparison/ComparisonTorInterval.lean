/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport

/-!
# Comparison preserves and detects Tor intervals

Source: Weil conjectures blueprint, `sec-six-functors/sk-cor-sf-direct-image-ctf/`
`lem-exc-comparison-tor-interval.md` (blueprint:
corollary-finite-tor-amplitude-under-comparison--1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- For a finite coefficient ring, bounded-below etale complexes have Tor amplitude in
`[a,b]` exactly when their canonical comparison pullback to the full small pro-etale site
has the same Tor amplitude, tested against every module sheaf on the respective site.
The pro-etale object is expressed in the recorded intrinsic constant-ring presentation
by the canonical exact coefficient realization, after the recorded termwise pullback.
The coefficient `ULift` is the one used by `proEtaleDerivedCategory`.
Source: blueprint `sec-six-functors/sk-cor-sf-direct-image-ctf/`
`lem-exc-comparison-tor-interval.md`; Stacks, Tags 099T, 099V, 08FZ, 08G0 and 08G1
(blueprint: corollary-finite-tor-amplitude-under-comparison--1).

Proof:
1. Put F = nu_T^*. The exactness and sheaf unit isomorphism of
`prop-weil-pbc-site-comparison-finite-level` imply that F preserves and reflects zero
sheaves. By `lem-sf-comparison-pullback-exact`, H^i(FC) = F(H^i(C)) for all complexes
and degrees. Thus cohomology vanishing is preserved and reflected without boundedness.
2. Suppose K has etale Tor amplitude in [a,b]. Testing with the coefficient ring,
using `lem-pc-kflat-resolution` and `proposition-open-direct-image-preserves-finite`, gives H^i(K) =
0 outside [a,b]. Upper smart truncation at b gives a representative zero above b. By
`lem-pc-kflat-bounded-flat-replacement`, replace it by a quasi-isomorphic flat complex
P zero above b. It is K-flat by `lem-pc-bounded-above-flat-kflat-site`, so P tensor N
computes K tensor^L N for every etale module sheaf N.
3. The Tor bound gives H^(a-1)(P tensor N) = 0 for every N. The universal-tensor
criterion `lem-weil-pbc-site-flat-opcycles-tor-criterion` makes
Q = coker(P^(a-1) -> P^a) flat. Lower smart truncation gives the flat complex
B = [Q -> P^(a+1) -> ... -> P^b]. The projection P -> B is a quasi-isomorphism,
since K has zero cohomology below a. Thus B represents K and is supported in [a,b].
4. By `corollary-finite-tor-amplitude-under-comparison`, FB has flat terms; exactness makes it
represent FK, by `def-sf-comparison-derived-pullback`. It is K-flat by
`lem-pc-bounded-above-flat-kflat-site`. The tensor computation of
`prose-03-02` shows that FB tensor M has no cohomology outside [a,b]
for every pro-etale module sheaf M. Canonical coefficient realization identifies the
fixed-scalar and intrinsic constant-ring module sheaves, their ordinary tensors and
cohomology. This proves the forward implication for the recorded
`def-weil-proetale-tor-amplitude`, including nonclassical test sheaves.
5. Part (1) of `lem-sf-comparison-pullback-exact` identifies the inverse image of the
constant coefficient ring with the constant ring and its ringed pullback with F.
Exactness identifies LF with termwise F. Apply the unbounded tensor comparison
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` to get
F(K tensor^L N) = FK tensor^L FN for every etale module sheaf N. Use the common
larger universe of `definition-small-pro-etale-site--1` and
`proposition-comparison-morphism-inverse-image`; site object and morphism universes remain
distinct. No boundedness of K tensor^L N is required.
6. Conversely, if FK has pro-etale Tor amplitude in [a,b], use FN as the test sheaf
for each etale N. Steps 1 and 5 give
F(H^i(K tensor^L N)) = H^i(FK tensor^L FN) = 0 outside [a,b]. The sheaf unit
isomorphism reflects this vanishing. Since N was arbitrary, this is exactly
`def-kun-tor-amplitude`, proving the reverse implication.
-/
theorem comparison_torAmplitudeIn_iff
    (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K.obj ↔
      Scheme.HasProEtaleTorAmplitude T A
        ((finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj
          ((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj) a b := by
  let F := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let e := F.mapDerivedCategoryPlusCompatibility.app K
  have hp := intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T a b _hab
    (((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj)
  have he : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T a b
        (F.mapDerivedCategory.obj K.obj) ↔
      ProEtale.DerivedCategory.torAmplitudeIn
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T a b
          (((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj) := by
    constructor
    · exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm
    · exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
  exact (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn (Λ := ULift.{u + 1, u} A)
    (K := K.obj)).trans
    ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      (Λ := ULift.{u + 1, u} A) a b K.obj).symm.trans (he.trans hp.symm))

end AlgebraicGeometry.ProEtale
