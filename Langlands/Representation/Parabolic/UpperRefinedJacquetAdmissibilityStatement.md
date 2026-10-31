# Admissibility of actual normalized upper refined Jacquet modules

Author: Worker 828.

This module states the closed proposition
`Langlands.Parabolic.UpperRefinedJacquetAdmissibilityStatement.{uF,uV}`.
It supplies no proof. It is the upper counterpart of the published clause
`Langlands.Parabolic.RefinedOppositeJacquetAdmissibilityStatement`.

## Parameters

The proposition quantifies over a prime `p`, a p-adic field
`F : PadicField p`, its supplied compatible `T : F.TopologicalData`, a
natural rank `n`, an ordered block shape `B` of `n`, an inner refinement
`S : BlockRefinement B`, a complex vector space `V : Type uV`, and a
representation `ρ : Representation ℂ (B.Levi F.Carrier) V` of the outer
product Levi. The field universe `uF` and the carrier universe `uV` are
independent. Rank zero, with the empty block shape, is included.

The installed topology is exactly `T.topology`. The product-Levi topology
and the subspace topology on `Geometric.refinedLevi F.Carrier B S` are the
induced topologies of the existing constructions. `Langlands.IsAdmissible`
means smoothness together with `Module.Finite ℂ` for the fixed submodule of
every open subgroup. The carrier `V` may be infinite dimensional.

## Assertion

The only hypothesis is `IsAdmissible ρ`, for an arbitrary representation of
the product `B.Levi F.Carrier`; no tensor decomposition is assumed. The
conclusion is admissibility of the exact representation
`T.normalizedRefinedJacquet B S ρ` of `Geometric.refinedLevi F.Carrier B S`.
Its carrier is the coinvariant quotient `Geometric.RefinedJacquetModule B S ρ`
by `Geometric.refinedUnipotent F.Carrier B S`, the product over the outer
blocks of the upper radicals of the inner refinements. The refined Levi acts
on it through the quotient action, twisted by the inverse half of the full
character `T.refinedLeviModulus B S`
(`PadicField.TopologicalData.normalizedRefinedJacquet_mk`).

## Original source and derived formulation

The original source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019, registered as
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Section III.3, pages 3–4, defines the quotient by the span of the
differences `π(n)v - v` and normalizes the Levi action by the inverse half
modulus. Theorem III.5.6 on page 7 states that the Jacquet module
`(π_N, V_N)` of an admissible representation `(π, V)` of `G` is an admissible
representation of `M`. Lemma III.5.4 and Proposition III.5.5 (pages 6–7)
provide the canonical-lift argument. Page 7 assumes a coefficient field from
that point on; the present statement uses complex coefficients.

The formulation is derived: it specializes Theorem III.5.6 to the reductive
group `B.Levi F.Carrier`, a product of general linear groups, and to its
parabolic subgroup that is the product of the upper block parabolics of the
inner shapes `S i`. The block indices, bundled modulus characters and universe
parameters are internal formalization choices, and match those of the
published opposite clause. The statement was extracted from task
5c9a0e18-0039-4f00-81bc-e103757b5a3a (weak upper Jacquet bounds under
induction), where it is used in the spectral step, and is also needed by
other geometric-lemma consumers.

No irreducibility, finite length, finite-dimensional carrier, tensor
factorization or chosen canonical lift is a hypothesis. The statement makes no
claim about exactness, adjunction, or the unnormalized Jacquet action.
