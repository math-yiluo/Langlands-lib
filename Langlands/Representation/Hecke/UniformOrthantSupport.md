# Common compact coefficient envelopes from positive orthant charts

This internal supporting unit implements the finite-box step of Renard,
*Représentations des groupes réductifs p-adiques* (2026), VI.2.4, printed
pp.141–142 / PDF pp.147–148. It combines the existing fixed-level compression
bound with finite positive charts and the central-cover compactness lemma.
Its geometric and numerical inputs remain explicit. It does not construct
Cartan charts, an Iwahori contraction family, a common dimension bound, or
vanishing Jacquet coinvariants on an actual reductive group.

The positive parameters are functions from a finite label type `Δ` to `ℕ`.
A monoid homomorphism `e` from their additive monoid, written multiplicatively,
maps them into the ambient group. `orthantBox Δ d` consists of parameters with
every coordinate strictly less than `d`. It is finite, including when `Δ` is
empty. `orthantBoxResidual e d T` is the finite set of products `e(n) t` for
parameters in that box and residual factors in a finite set `T`.

For every label, the compression theorem assumes an actual Iwahori contraction
at one compact open subgroup `K`, with contracting element the image of the
corresponding unit coordinate. Each Levi normalizes its unipotent subgroup.
Every positive parameter must conjugate `K` intersected with that unipotent
subgroup into `K`. The smooth representation has zero actual Jacquet
coinvariants for every label, and its finite-dimensional `K`-fixed space has
dimension at most `d`. A coordinate at least `d` can be split off as the
`d`-th power of its unit generator. The remaining positive factor satisfies the
upper-factor condition of the existing invariant-output vanishing theorem.
Consequently every `K`-invariant linear output vanishes there on every
`K`-fixed input. The nonzero outputs therefore lie in `orthantBox Δ d`.
The output space and representation carrier have independent universes.

The full coefficient theorem uses actual charts
`g = k₁ e(n) t k₂ z`, where both outer factors lie in a subgroup `J`,
the residual factor lies in `T`, and `z` belongs to the full abstract center.
It tests a vector and an algebraic-dual functional invariant at a subgroup `U`,
which may differ from the compression level `K`. Two explicit, uniform
containments require `k₁ K k₁⁻¹` and `(t k₂)⁻¹ K (t k₂)` to lie in `U`.
They make the transported functional and vector invariant under `K`.
Centrality preserves the fixed-vector property when the central factor acts.
There is no assumption that `T` normalizes `K`, no use of a scalar central
character, and no restriction to a selected proper subspace of the algebraic
dual.

`orthantSupportEnvelope H J e d T` is inversion, in a subgroup `H`, of the
literal preimage in `H` of
`J (orthantBoxResidual e d T) J Z(G)`. The coefficient support theorem applies
the chart to the inverse group element, so it bounds precisely the inverse
coefficients. This set is independent of the representation, vector and dual
functional. If `H` is closed, `J` is compact and contained in `H`,
`H` intersects the full center compactly, and `T` is finite, then the envelope
is compact by `isCompact_centralDoubleCover_preimage` and continuous inversion.

All arguments are elementary compositions of published lemmas, rather than
new external structural results. In particular, the actual rational norm
kernel can supply the central compactness inputs through
`RationalNormKernelCentralCover`, but constructing the other actual geometric
data, proving the class-uniform dimension and Jacquet-zero inputs, and
transporting all tested kernel representations and their full smooth duals
remain obligations of the exact uniform-support target. Its premises and
imported Lean/Markdown pairs are unchanged.
