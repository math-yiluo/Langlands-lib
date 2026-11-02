# Ordered actual-unit cocycles presenting line bundles

This module is an internal construction at every universe `u`. It supplies the
converse encoding from multiplicative transition units to closed ordered
cochains of the actual structure-sheaf units. It then gives every actual line
bundle on a compact scheme a finite affine-cover presentation by such a cochain,
with an actual isomorphism recovering its underlying sheaf by gluing.

For a scheme `X : Scheme.{u}` and a family `U : ι → X.Opens` with `ι : Type u`,
`transitionCochain U g` sends the tuple `σ : Fin 2 → ι` to the restriction of
`Additive.ofMul (g (σ 0) (σ 1))` to `Cech.inter U σ`. Its coefficient presheaf is
exactly `NilpotentUnitReduction.unitsPresheaf X.presheaf`: sections are the actual
units of the structure-sheaf section ring, with multiplication written as
addition. All ordered tuples are allowed, including repetitions.

`res_transitionCochain` computes restriction of the encoding of a pair to any
smaller open. `transitionCochain_pair` recovers the original overlap unit by
restricting to `U i ⊓ U j`. Conversely,
`transitionCochain_pairRestriction` states that encoding the pair restrictions
of any ordered one-cochain recovers that cochain. These two inverse identities
hold for arbitrary overlap units and one-cochains, without closedness, a full
cover, finiteness, affine opens, or compactness.

`d_transitionCochain` proves closedness from
`CocycleGluing.IsCocycle g`. On a triple tuple, its proof restricts the
multiplicative cocycle equation to the triple intersection, identifies it with
an equation of actual units, and writes it additively. Expanding the three terms
of the alternating Čech differential then gives zero. The reverse implication
uses the published `Cech.cocycle_add` equation, the restriction formula for the
encoding, and the underlying values of the units. Thus
`d_transitionCochain_eq_zero_iff` equates closedness of this cochain with the
original multiplicative transition equation. No cover condition is used.

`FinitePresentation M` records a finite ordered affine cover of `X`, actual
transition units on its pairwise overlaps, their cocycle equation, and an actual
module-sheaf isomorphism `M ≅ CocycleGluing.glued transitions`. The cover is the
published `Scheme.OrderedAffineCover`; its finite index type lies in `Type u`.
The order is used to carry the existing affine-cover data; the cochain in this
module still uses every ordered tuple, not only increasing tuples.

For a presentation `D`, `D.cochain` is the actual-unit ordered cochain obtained
by encoding `D.transitions`, and `D.closed` proves it closed. `D.cochain_pair`
recovers the transitions. Consequently `D.cochainIso` recovers `M` by gluing the
pair restrictions of that cochain itself. `D.isLocallyFreeRankOne` follows from
local freeness of the glued sheaf on a full cover and transport across `D.iso`.

`exists_finitePresentation` assumes only `CompactSpace X` and
`IsLocallyFreeRankOne M`. It applies the published
`Modules.BiCech.exists_frameCover` to choose a finite ordered affine cover with
a frame on each member. The published `CocycleGluing.frameCocycle` constructs
the transitions, `isCocycle_of_isTransition` proves their equation, and
`frameIso` supplies the actual gluing isomorphism. Thus
`nonempty_finitePresentation_iff` characterizes locally free rank-one sheaves
by the existence of this presentation on compact schemes. In particular every
`L : LineBundle X` has a presentation by applying the existence theorem to
`L.property`. There are no separation, reducedness, smoothness, projectivity,
field, or rational-point assumptions.

The provenance is an internal derivation from the published ordered Čech
complex, actual unit presheaf, transition-cocycle gluing, frame coefficients,
and finite frame-cover theorem. No external theorem translation or unpublished
prerequisite is used. This module does not identify the resulting cocycles with
actual sheaf cohomology, construct a cover-independent classifier, prove
refinement or pullback compatibility, establish a deformation theorem, or
prove Picard representability. Those remain separate obligations.
