# Upper positive reduction and incident quotient roots from root intersections

Module `Langlands.BruhatTits.IntegralModels.UnramifiedRootIntersectionReduction`.

This internal supporting module works over the maximal unramified extension
`K = inertiaFixedField F` of a nonarchimedean local field `F`, in arbitrary
universe `u`. It reproves two published arguments under a weaker hypothesis on
the supplied model:

- the integral-section criterion of `unramifiedRootPositiveReduction`
  (module `UnramifiedRootPositiveReductionProof`);
- the incident-root survival argument of `UnramifiedIncidentRootSurvival` and
  `UnramifiedIncidentQuotientRoots`.

The published versions assume the full neutral-point equality
`D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)`,
which is KP Theorem 8.3.13 over `K` (`UnramifiedParahoricModelStatement`,
still unproved). The proofs only use its consequence on root groups. This
module therefore assumes that consequence alone.

## Setting

`C : MaximalUnramified.BuildingData F G` is a building datum of a group `G`
over `K`, `Ω` is a set of apartment points, and `D` is relative-component model
data over `fixedFieldIntegers F`.

## Declarations

- `HasRootFixerIntersections C Ω D` (a `Prop`). For every relative root `b` of
  `C.i`,
  `rootGroupPoints C.i b ⊓ D.neutral.integralPoints = C.apartment.rootFixer b Ω`.
  For the recovered fixer models of this project it is supplied by the
  published `rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer`.
- `mem_positivePoints_iff_of_rootFixerIntersections`. Assume these
  intersections, `Ω` nonempty, a split integral torus
  `T : IntegralTorusData D C.S C.i`, and a supplied quotient `Q` with
  `Q.IsReductiveQuotient`. Then a neutral integral point `g` of the root group
  of `a` satisfies
  `g ∈ Q.positivePoints ↔ ∃ x ∈ Ω, g ∈ C.apartment.filtrationPlus x a 0`.
- `singleton_reductiveReduction_eq_one_iff_of_rootFixerIntersections`. For
  `Ω = {x}` and a neutral integral section `z` whose generic point lies in the
  root group of `a`, `Q.reductiveReduction z = 1` holds exactly when that
  generic point lies in `filtrationPlus x a 0`.
- `quotient_root_of_depth_boundary_of_rootFixerIntersections`. For `Ω = {x}`,
  suppose `g ∈ C.apartment.filtration x a 0` lies outside the product
  `filtrationPlus x a 0 · doubleRootGroupPoints C.i a`. Then the canonical
  specialization `T.characterSpecialization hT a` is a relative root of
  `T.specialFibreInclusion ≫ Q.projection`.
- `exists_quotient_root_of_incidentAffineRoot_of_rootFixerIntersections`. For
  `Ω = {x}`, let `ψ ∈ C.affineRoots` vanish at `x`. Then there is a relative
  root `a` with `ψ.linear = rootForm C.i a` whose canonical specialization is
  a root of the quotient.

## Proofs

The positivity criterion follows the published proof of
`unramifiedRootPositiveReduction` line by line. The only change is that each
use of the zero-fixer root intersection is replaced by the hypothesis
`HasRootFixerIntersections`.

- The identity lies in both sides.
- For `g ≠ 1`, the relative rank-one factorization
  `rootRankOneFactorization` supplies an ordered normalizing opposite pair
  `p`. Its Weyl action shows that `-a` is a relative root.
- If `g` is positive but has depth zero at every point of `Ω`, axiom V5 at
  these points gives depth zero to both opposite factors. The root
  intersections then make them integral. The integral opposite-factor
  necessity theorem `not_mem_positivePoints_of_integral_oppositeFactors`
  excludes positivity, a contradiction.
- Conversely, suppose `g` has positive depth at some point but is not
  positive. Then `henselianIntegralOppositeFactors`, over the Henselian
  discrete valuation ring `fixedFieldIntegers F` with algebraically closed
  residue field, makes the first opposite factor integral. The root
  intersection gives it nonnegative depth at that point, and V5 contradicts
  the positive depth of `g`.

The singleton reduction criterion combines this with
`ker_reductiveReduction`, the fppf-quotient clause of `IsReductiveQuotient`,
and injectivity of the neutral integral point map.

The depth-boundary and incident-root theorems repeat the published proofs of
`unramified_quotient_root_of_depth_boundary` and
`exists_unramified_quotient_root_of_incidentAffineRoot`. Integrality of the
zero-depth point comes from the root intersections and `rootFixer_singleton`.
The rest of the argument is unchanged:

1. If the root were absent from the quotient, `quotient_subgroup_eq_double_of_absent_root`
   would identify the quotient root functor with the doubled one.
2. Perfect-residue lifting would then supply an integral point of the doubled
   root group with the same reduction.
3. The singleton reduction criterion would place the quotient in strict depth,
   contradicting the depth-boundary hypothesis.

`C.apartment.exists_rootDepthBoundary_of_affineRoot` supplies the boundary
point of an ordinary affine root.

## Provenance

This is internal derived content. It reorganizes the published proofs named
above, which formalize the integral-section criterion of Kaletha–Prasad
Lemma 8.4.4 and the survival of affine roots vanishing at the point in the
reductive quotient (KP Proposition 9.4.23 over `K`). The source is
Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. No new literature assertion is
made. The module proves neither `UnramifiedParahoricModelStatement` nor the
published `UnramifiedRootPositiveReductionStatement` in a new form, and it
constructs no model, torus or quotient.
