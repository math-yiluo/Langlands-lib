# Actual quasi-split descent from a supplied pinned Galois action

Let `k` and `K` be fields in an arbitrary universe `u`, with a supplied finite
Galois `k`-algebra structure on `K`. Let `G` be an actual affine group scheme
over `Spec K`, let `p` be a supplied complete split pinning, and let
`ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut` be a supplied based full-root-datum
action. This internal construction builds compatible actual group-and-Borel
descent data and an effective quasi-split solution over `k`.

The generic lemma `Descent.semilinearComponent_naturality` converts the
equivariance square
`eB.hom ≫ i = (baseChange b).map i ≫ eG.hom`
into the corresponding square for the normalized descent components
`baseChangeIdIso ≪≫ e.symm`. Its proof composes with the isomorphism `eG`,
uses the supplied square and inverse identities, then uses naturality of the
canonical identity-pullback comparison. No closedness, finiteness, or field
hypothesis is needed for this lemma.

`SplitPinning.galoisSemilinearBorelIso` specializes the actual semilinear
negative-Borel isomorphism to the ring equivalence underlying each Galois
automorphism and its based action. `galoisSemilinearBorelIso_hom_comp` is its
actual equivariance square with the pinned ambient lift and the actual
negative-Borel inclusion.

`galoisBorelOverlap` assembles the normalized Borel component maps using the
same actual finite-Galois double-overlap decomposition as `galoisDatum`.
`pullIso_galoisBorelOverlap` recovers each exact normalized Borel map.
`galoisBorelOverlap_hom_comp` proves that this assembled overlap and the
ambient overlap respect the actual Borel inclusion. The proof restricts both
sides to every finite overlap component, uses the exact recovery formulas
for both overlaps and pullback of the inclusion, and applies
`semilinearComponent_naturality`. Faithfulness of restriction along the
actual finite coproduct decomposition gives equality of the actual global
group-scheme maps.

`range_galoisDatum_negativeBorelHom` also records invariance of the Borel
subgroup range over the full actual overlap. This is equality of the existing
all-relative-scheme-test subgroup functors, obtained from the actual
inclusion square and invariance of range under an isomorphic source.

`galoisBorelDatum` takes this explicit Borel overlap as its overlap
isomorphism. The actual Borel inclusion is closed, by its geometric-Borel
property. The existing `cocycle_of_closedSubgroup_lift` therefore proves the
Borel cocycle by composing with the inclusion over the triple overlap,
applying the ambient cocycle, and cancelling the closed inclusion.
`compatible_galoisBorelDatum` records the proved inclusion square as
compatibility of the two data. `pullIso_galoisBorelDatum` retains exact
recovery of the chosen Borel components.

`galoisQuasiSplitSolution` applies the actual effective
`Datum.quasiSplitSolution` construction to these data, the connected
reductivity supplied by the pinning, and its actual geometric Borel. Its
output contains actual affine descended group and Borel objects, their
effective-descent solutions and pullback isomorphisms, an actual inclusion,
the exact pullback recovery equation, descended connected reductivity,
and the geometric-Borel property of the descended inclusion.
`isQuasiSplit_galoisQuasiSplitSolution` packages those properties as
quasi-splitness of the descended ground-field group. The finite-dimensional
extension supplies the algebraicity needed by the effective descent
construction; no perfection or characteristic restriction is added.

The provenance is internal: the construction combines the imported actual
pinned semilinear maps, finite-component assembly, monic closed-subgroup
cocycle argument, and effective group-and-Borel descent. It assumes the
finite Galois extension, complete pinning, and based action; their
unconditional construction remains necessary for the host theorem.
It does not construct a full-centre adjoint quotient or the inner local
comparison and discrepancy cocycle required by
`QuasiSplitInnerFormExistenceStatement`.
