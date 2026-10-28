# Simultaneous coefficient and radius transport of scalar rational quotients

Worker 56 derives this construction from the published scalar rational
transport, radius restriction and coefficient-equivalence APIs. The new map
changes the coefficient presentation and decreases the newly adjoined radii
at the same time. Its values determine it uniquely among bounded maps, and
the order of the two changes does not matter.

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation`.
This is a local quotient construction; analytic-domain representability
and analytic sites remain separate obligations.

## Inputs and actual carriers

Let `K` be a complete ultrametric normed field. Let `A` and `B` be actual
`PresentedAffinoidAlgebra K` values. Their finite arities, positive polyradii
and closed ideals may differ. Choose one finite new-variable block `Fin m`,
positive polyradii `s` and `t` on it, and `hts : ∀ j, t j ≤ s j`.
Choose scalar series representatives `g, f j` over the presentation of `A`
and `g', f' j` over that of `B`. Assume an actual bounded unital
`K`-algebra map `φ : A → B` and the matching class equalities

\[
 \varphi(\bar g)=\bar g',\qquad
 \varphi(\bar f_j)=\bar f'_j.
\]

The source `B_{A,s}` is the existing enlarged scalar weighted-series
quotient by the closed generated old coefficient relations and
`g Y_j - f_j`. The target `B_{B,t}` is the corresponding actual quotient
over `B` at radius `t`. Both carry their existing quotient norms.
No representative of each individual value `φ(a)` is chosen.

## Construction, uniqueness and norm bound

Write `P_s` for the published `presentationTransport` at radius `s` and
`R^B_{s,t}` for the published scalar `radiusMap` over `B`. Define

\[
 M_{\varphi;s,t}=R^B_{s,t}\circ P_s:B_{A,s}\longrightarrow B_{B,t}.
\]

This is `presentationRadiusTransport`. It is an actual bounded algebra map,
constructed by composition of the existing maps, rather than an assumed
localization or analytic-domain map.

`presentationRadiusTransport_baseMap` and
`presentationRadiusTransport_fraction` give

\[
 M_{\varphi;s,t}(i_{A,s}(a))=i_{B,t}(\varphi(a)),\qquad
 M_{\varphi;s,t}(Y_j)=Y_j.
\]

The proofs apply the respective coefficient and fraction formulas of the
two component maps. `eq_presentationRadiusTransport` proves uniqueness
among all bounded maps with these two families of values, using the
published scalar coefficient/fraction extensionality theorem.

`norm_presentationRadiusTransport_le` retains every supplied nonnegative
coefficient bound exactly:

\[
 0\leq c,\quad \forall a,\ \|\varphi(a)\|\leq c\|a\|
 \quad\Longrightarrow\quad
 \|M_{\varphi;s,t}(b)\|\leq c\|b\|.
\]

It composes the contraction estimate for `R` with the unchanged bound for
`P`. The value `c = 0` is allowed. The contractive specialization is
`norm_presentationRadiusTransport_le_of_contractive`.

## Order independence and composition

`radiusMap_presentationTransport` proves equality of bounded maps

\[
 R^B_{s,t}\circ P_s=P_t\circ R^A_{s,t}.
\]

The proof uses scalar coefficient/fraction extensionality and the four
existing formulas on both sides. `presentationRadiusTransport_eq`
therefore gives the second expression for the constructed mixed map.

`presentationRadiusTransport_self` recovers `P_s` when `t = s`.
`presentationRadiusTransport_id` recovers `R^A_{s,t}` for the identity
coefficient map and identical representatives. In particular, their
combination and the existing radius identity give the identity map when
both changes are identities.

For another presented coefficient algebra `C`, matching scalar data, an
actual bounded map `ψ : B → C`, and `v ≤ t`, the theorem
`presentationRadiusTransport_comp` states

\[
 M_{\psi\circ\varphi;s,v}
   =M_{\psi;t,v}\circ M_{\varphi;s,t}.
\]

Its explicit class-matching equations are obtained by applying `ψ` to the
first matching equations and composing with the second ones. The radius
inequality is transitivity. Again, the proof compares coefficient and
fraction values, so it proves equality of the bounded maps themselves.

For a supplied bounded coefficient equivalence `e`, the theorem
`presentationTransport_eq_presentationEquiv` identifies the general map
at one radius with the underlying forward bounded map of the published
`presentationEquiv`. This is proved by that equivalence's coefficient
and fraction characterization. It does not make the mixed map invertible
when the radius is decreased.

## Continuous spectra and inequality subspaces

`presentationRadiusSpectrumMap` is continuous seminorm precomposition
along `M`, with direction

\[
 \mathcal M(B_{B,t})\longrightarrow\mathcal M(B_{A,s}).
\]

Its evaluation formula is definitional.
`presentationRadiusSpectrumMap_naturality` proves equality of the two
continuous structural paths to `\mathcal M(A)` by evaluating the mixed
coefficient formula.
`radiusSpectrumMap_presentationSpectrumMap` gives the corresponding
commuting square for the two existing spectrum pullbacks. Its proof
evaluates the bounded-map order-independence equality, so the direction
of composition is contravariant.

The scalar `spectrumToLocus` bundles the existing structural map with its
proved weighted rational inequalities. This forward continuous map
requires no completeness assumption. It makes no surjectivity claim.

`presentationRadiusLocusMap` is the continuous map
`locus K B t g' f' → locus K A s g f` given by coefficient seminorm
precomposition with `φ`. Matching classes rewrite the target inequalities,
and multiplication of `t j ≤ s j` by the nonnegative denominator value
gives the source inequalities. Its topology is the inherited subspace
topology, and its evaluation formula is definitional. This construction,
its equal-radius agreement with `presentationLocusMap`, and its
contravariant composition theorem omit completeness of `K`.

Finally, `spectrumToLocus_presentationRadiusTransport` proves equality of
the two continuous maps to the source inequality subspace: first pull back
the quotient seminorm and then take its coefficient point, or first take
the target coefficient point and apply the mixed locus map. Subtype and
seminorm extensionality reduce this equality to the mixed coefficient
formula.

## Provenance and limits

The original source context is Vladimir Berkovich, *Non-Archimedean
analytic spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.6(i), printed/PDF page 8, supplies relative weighted
restricted series and their norm; Definition 2.1.11 on that page supplies
the bounded-map dual category. Exercise 2.2.2(ii), page 9, supplies
common-denominator rational equations and inequalities.

The simultaneous map, unchanged bound and coherence laws are internal
derivations from the published concrete constructions, not separately
numbered results attributed to that source. The source's rational-domain
conclusion requires an additional no-common-zero hypothesis. None of the
claims here assert that conclusion.

The construction allows empty old or new blocks, arbitrary positive radii,
trivial valuations and zero quotients. No proper-ideal, unit-ideal,
injectivity, surjectivity, isometry, denominator invertibility, reverse
radius map, arbitrary presentation independence, sheaf, atlas or analytic
site is asserted. Completeness is needed for the scalar coefficient
comparison used in `M`, but not for the independently constructed locus
maps or scalar forward structural map.
