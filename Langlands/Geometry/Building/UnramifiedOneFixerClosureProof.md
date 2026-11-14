# Pointwise fixers extend to affine topological closures

`Langlands.Geometry.Building.unramifiedOneFixerClosure.{u}` proves the exact
Library proposition
`Langlands.Geometry.Building.UnramifiedOneFixerClosureStatement.{u}`.
It uses the existing statement without changing its hypotheses or definitions.

## Exact scope

For every nonarchimedean local field `F : Type u`, in equal or mixed
characteristic, put `K = inertiaFixedField F`. The theorem applies to every
affine group scheme `G` over `F`, every supplied
`C : MaximalUnramified.BuildingData F (baseChanged F K G)`, every translating
point `g` in the rational points of that base change, and every nonempty
`Ω : Set C.Apartment` bounded above under every real affine functional.
It equates the pointwise fixers of `g · Ω` and `g · closure Ω` after
intersection with
`characterValuationKernel (MaximalUnramified.valuation F) (baseChanged F K G)`.
Closure uses precisely `unramifiedApartmentTopology C`.

The supplied data already contain connected reductivity of the base change,
the chosen maximal split torus and the compatible apartment data. The proof
derives smoothness from that connected reductivity. Its private affineness
instance uses stability of affine morphisms under base change.
There is no additional existence, apartment-axiom, or characteristic premise.
The rank-zero case is included. The nonemptiness premise is accepted by the
theorem but is unnecessary for this proof route.

## The topological lemmas

The generic lemmas are in `KPApartmentData`. They use
`D.affineFunctionalTopology`, the initial topology of all real affine maps
`D.Apartment →ᵃ[ℝ] ℝ`. In the final specialization this is definitionally
the statement's `unramifiedApartmentTopology C`.

The private `continuous_affineFunctional` proves continuity directly from
the infimum of the induced topologies.
The private `isClosed_weakSignRegion` observes that
`{t | sign t = 0 ∨ sign t = sign c}` is `Iic 0` when `c < 0`, the singleton
`{0}` when `c = 0`, and `Ici 0` when `c > 0`.

`isClosed_facetClosure_affineFunctionalTopology` expresses the combinatorial
closed facet as the intersection of the inverse images of these closed weak
sign regions under its affine roots. Consequently that closed facet is
topologically closed. This concerns the closure of a single facet as defined
by weak signs; it does not identify an arbitrary set's topological closure
with the union of closed facets meeting it.

`isClosed_affineFixedSet` proves that the fixed points of any affine
self-map `e` of the reduced apartment form a closed set. It writes this set as
the intersection, over all real affine functionals `f`, of the scalar
equalizers `(f.comp e) x = f x`. The reverse set inclusion uses the separating
root coordinates of the reduced translation space:
`eq_zero_of_rootForm_eq_zero i` applied to `e x -ᵥ x`, and the affine
functionals with origin `x` and constant term zero.
Both functions in each scalar equalizer are continuous by the definition
of the topology. No topology on the reduced building is used.

## Finite facet decomposition

`smul_apartmentMap_eq_of_mem_affineClosure_of_finite_facets` assumes connected
reductivity, maximality of the split torus, and AS4 for the apartment's
extended affine roots. It proves the following stronger intermediate result:
if `facet D.affineRoots '' Ω` is finite and a rational point `h` fixes the
quotient image of every point of `Ω`, then `h` also fixes the quotient image
of every point of the affine topological closure of `Ω`.

Write `Ω` as the union of its intersections with the finitely many facets
it meets. Closure commutes with this finite union.
For each such facet choose `p ∈ Ω` defining it. The published
`exists_normalizer_eq_on_translated_facetClosure`, applied to fixation of
`D.apartmentMap p`, supplies a normalizer element `n` whose affine action
agrees with `h` in the quotient throughout the closed facet of `p`.
On the intersection of the chosen facet with `Ω`, the published
`apartmentMap_injective` converts quotient fixation to `n · y = y`.
Thus this intersection lies in the intersection of the closed facet and
the affine fixed set of `n`. The two topological lemmas show that this
intersection is closed, so it contains the closure of the original piece.
The normalizer comparison then gives fixation there. Taking the finite
union proves the intermediate result.

## Specialization to the maximal unramified field

The published
`IntegerValuationBuildingData.isAffineRootSystemWithRankZero_affineRoots`
applies because `MaximalUnramified.exists_order_eq_one F` supplies a unit
of order one, obtained from a base-field uniformizer.
Its `finite_facets_meeting` theorem applies to the target's exact affine
boundedness hypothesis.
AS4 follows from the supplied building data's opposite factor pairs by
`mem_or_two_smul_mem_affineRoots_of_oppositePairs`.

For an element `h` fixing the translated image `g · Ω`, elementary action
identities show that `g⁻¹ * h * g` fixes the original image of `Ω`.
Apply the generic finite-facet lemma and translate back by `g`.
Retain `h`'s original character-valuation-kernel membership throughout.
This proves the forward inclusion without a separate kernel-normality
argument. The reverse inclusion is the existing
`characterValuationKernel_inf_pointwiseFixer_closure_le`.

## Provenance

This is a derived proof using the published Library's actual quotient,
affine normalizer action, generic apartment injection and bounded-facet
finiteness theorem. Its generic topological lemmas are internal consequences
of the existing initial topology, affine root sign definitions and separating
root coordinates.

The original source context and exact citations are recorded in the unchanged
`UnramifiedOneFixerClosureStatement.md`: Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 7.4.4(3), §7.7 and
Proposition 7.7.5(1), read with the authors' 1 November 2024 corrections.
The implemented proof follows the finite-facet argument above rather than
reconstructing the source's full sharp-fixer product identification.
