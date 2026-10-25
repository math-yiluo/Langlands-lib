# Actual opposite canonical lifts in product Levis

This module states two canonical-lift assertions for arbitrary admissible
representations of a product Levi. It proves neither assertion. All three
declarations are Prop-valued definitions in `Langlands.Jacquet`.
The closed entry is `RefinedOppositeCanonicalLiftStatement.{uF,uV}`.

For every prime `p`, finite p-adic field `F`, supplied `TopologicalData T`,
natural rank `n`, block shape `B`, refinement `S`, and complex carrier `V`,
the entry conjoins `RefinedOppositePowerKernelJacquetClause F T B S V` and
`RefinedOppositeStableImageJacquetBijectiveClause F T B S V`.
The field and carrier universes are independent. Each clause installs the
topology and product-Levi topological-group structure supplied by `T`.

The representation `ρ` is an arbitrary representation of `B.Levi F.Carrier`
on `V`. Its only representation hypothesis is `IsAdmissible ρ`, which supplies
smoothness and finite-dimensional fixed spaces for every open subgroup.
There is no irreducibility, finite length, tensor decomposition, chosen
canonical lift, or finite-dimensionality assumption on the whole carrier.
Restriction to a single GL factor is not assumed to preserve admissibility.

## Actual compact opens and contraction

The quantified family `K i` consists of open subgroups of
`GeneralLinear (B.size i) F.Carrier`. Each has its own compactness witness
`hK i` and satisfies `(S i).HasBlockIwahoriFactorization T (K i)`.
The product subgroup `KP` is the existing
`CuspidalSupport.leviPiOpenSubgroup T B K`. Its underlying subgroup is
literally `Subgroup.pi Set.univ (fun i => (K i).toSubgroup)`.
Its openness is supplied by the finite product topology; its compactness
`hKP` is the published `isCompact_leviPiOpenSubgroup T B K hK`.
Neither is an additional hypothesis about an unspecified product.

For each outer block `i`, the tuple
`a i : Fin (S i).length → F.Carrierˣ` satisfies the existing upper strict
contraction predicate `(S i).IsStrictlyContracting T (a i)`. The element used
for compression is the actual tuple

```lean
g : B.Levi F.Carrier :=
  fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
```

It contracts the lower radical in every factor: conjugation multiplies a
lower off-diagonal block indexed by `r > s` by `a i s / a i r`, whose absolute
value is less than one. The block Iwahori predicates already include the
corresponding conjugation containments. Inversion reverses the order of the
three subgroup factors, and taking their finite product gives the opposite
Iwahori factorization needed for this product setting. These observations
justify the derived statement; the module does not prove those geometric
implications.

## The quotient maps and the two conclusions

Let `N` be `Geometric.refinedOppositeUnipotent F.Carrier B S`, the actual
product of the inner opposite radicals. Let `M` be
`Geometric.refinedLevi F.Carrier B S`, the actual product of the embedded
inner diagonal Levis. The proof of `M ≤ Subgroup.normalizer N` is obtained
directly from the existing `refinedOppositeLeviNormalizer`: on `m ∈ M`,
its value has underlying ambient element `m`, and its membership proof is
the required normalizer membership. No compatibility certificate is assumed.

Write `X = fixedVectors ρ KP.toSubgroup`. The published
`compressedAction ρ hρ KP hKP g` is the endomorphism `C` of `X` that first
applies `ρ g` and then normalized compact averaging.

The first clause says that the published submodule
`powerKernelSup ρ hρ KP hKP g`, the supremum of the kernels of `C^r` for
all natural `r`, equals the kernel of
`fixedJacquetMap ρ N M hMN KP.toSubgroup`.
The latter map is the actual quotient map restricted to `X`, with values
in the vectors fixed by `KP.toSubgroup.comap M.subtype` for the unnormalized
descended action `Jacquet.action ρ N M hMN`. Thus its kernel consists
exactly of the `KP`-fixed vectors killed in the actual opposite coinvariants.

The second clause asserts bijectivity of the existing
`stableImageJacquetMap ρ hρ KP hKP g N M hMN`. Its domain is
`stableImage ρ hρ KP hKP g`, the intersection of the ranges of all `C^r`
inside `X`. Its codomain is the same actual fixed-vector module just
described. Its value is the actual Jacquet quotient of the stable-image
vector. No inverse, arbitrary isomorphism, alternative quotient, or
stabilization premise is supplied.

Rank zero, empty outer products, one-block inner shapes, and the zero
representation are included. There is no positive-rank, nonempty-product,
proper-parabolic, or nonzero-representation premise. The strict inequalities
are vacuous when an inner shape has at most one block. For the empty outer
product the ambient group, radical and Levi are trivial; the compression is
the identity and the same formulations apply.

## Source and derivation

The source is Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter III, *Induced representations and the Jacquet module*,
revision April 29, 2019; registered as `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The original was read on pp.1–7; the formulas on pp.4–7 were inspected as
images. No separate project errata file was found.

The provenance is derived. The reductive-group setting on p.1 permits the
finite product of the outer GL factors. Apply section 4's Iwahori
factorization and section 5's opposing-parabolic setup (p.5) to the product
opposite parabolic with radical `N`, common Levi `M`, compact subgroup `KP`,
and contracting element `g`. Lemma III.5.4 (p.6) supplies the generalized
kernel description; Proposition III.5.5 (p.7) supplies the canonical
projection isomorphism. These apply to arbitrary admissible representations
of this reductive product, with no tensor factorization.

The formal operator uses normalized compact averaging. In the source's
coset-sum formulation, III.5.1 (pp.5–6) gives
`τ_g = d C`, where `d = [KP : KP ∩ g KP g⁻¹]` is a positive finite integer
viewed in `ℂ`. Multiplication by this nonzero scalar does not change the
kernels or ranges of powers. Admissibility makes `X` finite-dimensional,
so the source's sufficiently high image equals the intersection of all
power ranges used here. The source normalizes the Jacquet action; its
normalizing character is trivial on the compact Levi intersection, so its
fixed space agrees with the unnormalized codomain here. These operator,
stabilization, and fixed-space identifications are part of the intended
derivation, not added premises or proofs in this module.

The field restriction preceding III.5.5 and the warning after III.5.7
(p.7) are respected by using complex coefficients. No claim for arbitrary
Noetherian coefficient rings is made. The chosen block coordinates,
independent universes, and closed conjunction are internal packaging.

This statement supports refined opposite-Jacquet admissibility. It does
not prove admissibility, normalized-action compatibility, nested-subgroup
compatibility, second adjointness, transitivity, multiplicity comparison,
or the irreducible-head theorem. Its exact proof remains a separate task.
