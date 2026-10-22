# Prime-to-`p` finite adeles of the rationals

Author: Worker 300.

This module builds the finite adeles of `ℚ` away from a natural number `p`. It
uses the same completions, completed integers and restricted-product topology as
the published full model `Langlands.Global.FiniteAdeles ℚ`. It also constructs
the diagonal `ℚ`-algebra structure, restriction from the full finite adeles, and
the compact open subring of elements integral at every retained place. One lemma
shows that, for prime `p`, exactly one finite place is left out.

## Index set

`PrimeToFinitePlace p` (an `abbrev`, `p : ℕ`) is the subtype

```text
{v : FinitePlace ℚ // (p : 𝓞 ℚ) ∉ v.asIdeal}
```

of the finite places of `ℚ` (nonzero prime ideals of `𝓞 ℚ`, imported from
`Langlands.Global.Adelic`). No primality hypothesis is imposed here: for every
natural number `p`, the subtype keeps exactly the places whose prime ideal does
not contain the image of `p`.

Primality is used only in the interpretation lemmas at the end of the module:

- `prime_natCast_ringOfIntegers (p : ℕ) (hp : p.Prime) : Prime (p : 𝓞 ℚ)`.
- `natCast_mem_asIdeal_iff (p : ℕ) (hp : p.Prime) (v : FinitePlace ℚ) :
  (p : 𝓞 ℚ) ∈ v.asIdeal ↔ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)}`.
- `existsUnique_finitePlace_natCast_mem (p : ℕ) (hp : p.Prime) :
  ∃! v : FinitePlace ℚ, (p : 𝓞 ℚ) ∈ v.asIdeal`.

As in every other public declaration of the module, `p` is an explicit argument.

So, for prime `p`, `PrimeToFinitePlace p` consists of all finite places except
the single place whose prime ideal is `(p)`. This is the place commonly called
"the place `p`". This module does not identify that place or its completion with
`ℚ_p` or with `Nat.Primes`. A comparison with products indexed by natural primes
is explicitly out of scope.

## The ring and its topology

`PrimeToFiniteAdeles p` (an `abbrev`) is Mathlib's actual restricted product

```text
Πʳ v : PrimeToFinitePlace p, [FiniteCompletion ℚ v.1, v.1.adicCompletionIntegers ℚ]
```

relative to the default `Filter.cofinite`. Here `FiniteCompletion ℚ v` is the
published alias for `v.adicCompletion ℚ`. Its elements are families `(a_v)` with
`a_v` in the completion at `v` and `a_v` integral for all but finitely many
retained `v`. The ring operations are Mathlib's coordinatewise restricted-product
operations, and the topology is Mathlib's restricted-product topology. That
topology is the final topology of the stages indexed by cofinite sets `S` of
retained places: the stage for `S` consists of the families that are integral at
every place of `S`, so non-integral coordinates occur only in the fixed finite
complement of `S`. Each stage carries the topology induced from the full product
of the completions, which is the product of the integer rings on `S` and the
completions off `S`. Neither the ring nor its topology is replaced by an
isomorphic model, and the topology on the whole ring is not the coarser subspace
topology from the full product. Because the type is an `abbrev`, all these
instances are the restricted-product ones by definition.

The instance `IsTopologicalRing (PrimeToFiniteAdeles p)` is Mathlib's
`RestrictedProduct.isTopologicalRing`. It is applied with the openness of every
local completed-integer ring (`Valued.isOpen_valuationSubring`), exactly as
Mathlib does for `FiniteAdeleRing`.

## Diagonal `ℚ`-algebra structure

`primeToDiagonal p : ℚ →+* PrimeToFiniteAdeles p` sends `x` to the family
`v ↦ algebraMap ℚ (FiniteCompletion ℚ v.1) x`. Each coordinate is the image of
`x` in the completion at `v`, under the completion's existing `ℚ`-algebra map
`IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion`. This is the
completion embedding used by Mathlib's diagonal `FiniteAdeleRing.algebraMap`, so
the coordinates agree by definition with those of the full diagonal adele. The
restricted-product condition is
transported from the full diagonal adele `algebraMap ℚ (FiniteAdeles ℚ) x`. That
adele has the same coordinates, and the injective inclusion
`PrimeToFinitePlace p → FinitePlace ℚ` carries the cofinite filter into the
cofinite filter. The ring-homomorphism laws hold coordinatewise because each
coordinate map is a ring homomorphism.

The `Algebra ℚ (PrimeToFiniteAdeles p)` instance is
`(primeToDiagonal p).toAlgebra`. Thus scalar multiplication by `x : ℚ` is
multiplication by the diagonal element. The `rfl` lemmas recording this are:

- `primeToFiniteAdeles_algebraMap_eq`: `algebraMap ℚ (PrimeToFiniteAdeles p) = primeToDiagonal p`.
- `primeToDiagonal_apply` and `primeToFiniteAdeles_algebraMap_apply`: the
  coordinate at `v` of the diagonal image of `x` is
  `algebraMap ℚ (FiniteCompletion ℚ v.1) x`.

## Restriction from the full finite adeles

`primeToFiniteRestriction p : FiniteAdeles ℚ →A[ℚ] PrimeToFiniteAdeles p` is a
continuous `ℚ`-algebra homomorphism. It forgets the coordinates at the omitted
places, so `a ↦ (v ↦ a v.1)`. The restricted condition is the full adele's
cofinite integrality condition, pulled back along the injective inclusion of
index sets. The additive, multiplicative and unit laws, and commutation with the
two diagonal maps, hold by definition. Continuity is Mathlib's
`RestrictedProduct.mapAlong_continuous`, applied with index map `Subtype.val`
(which tends cofinitely to cofinitely by injectivity) and identity coordinate
maps. It is therefore continuity for the actual restricted-product topologies on
both sides.

- `primeToFiniteRestriction_apply`: `primeToFiniteRestriction p a v = a v.1`.
- `primeToFiniteRestriction_algebraMap`: restriction sends
  `algebraMap ℚ (FiniteAdeles ℚ) x` to `algebraMap ℚ (PrimeToFiniteAdeles p) x`.

## The integral subring

`primeToIntegralFiniteAdeles p : Subring (PrimeToFiniteAdeles p)` is the set of
`a` with `a v ∈ v.1.adicCompletionIntegers ℚ` for every retained `v`
(`mem_primeToIntegralFiniteAdeles`, by `Iff.rfl`). The subring axioms are the
corresponding closure properties of each local valuation subring.

- `primeToIntegralInclusion p : primeToIntegralFiniteAdeles p →+* PrimeToFiniteAdeles p`
  is the subring inclusion `Subring.subtype`.
  `primeToIntegralInclusion_apply` states that it is the coercion, and
  `continuous_primeToIntegralInclusion` states that it is continuous for the
  subspace topology.
- `primeToIntegralRestriction p : integralFiniteAdeles ℚ →+* primeToIntegralFiniteAdeles p`
  is `RingHom.restrict` of the restriction homomorphism. It maps the published
  `integralFiniteAdeles ℚ` into the prime-to-`p` integral subring, because a
  family integral at every finite place is integral at every retained place.
  - `coe_primeToIntegralRestriction`: its underlying adele is
    `primeToFiniteRestriction p a`.
  - `primeToIntegralRestriction_apply`: its coordinate at `v` is `a v.1`.
  - `primeToIntegralInclusion_comp_restriction`: integral restriction followed by
    the inclusion equals the inclusion of `integralFiniteAdeles ℚ` followed by
    `primeToFiniteRestriction p`.
  - `continuous_primeToIntegralRestriction`: it is continuous for the subspace
    topologies.

## Compact open

`isOpen_primeToIntegralFiniteAdeles` proves openness in the restricted-product
topology by `RestrictedProduct.isOpen_forall_mem`, from the openness of every
local valuation subring.

`isCompact_primeToIntegralFiniteAdeles` copies the published proof of
`isCompact_integralFiniteAdeles` for the retained index set. The imported theorem
`isCompact_adicCompletionIntegers ℚ v.1` makes each local completed-integer ring a
compact space. Their product is compact by Tychonoff. Mathlib's
`RestrictedProduct.structureMap` from this product is continuous into the
restricted product (`isEmbedding_structureMap`). Its range is exactly the
everywhere-integral locus (`range_structureMap`), so that locus is compact as a
continuous image. Together these show that the integral subring is a compact open
subring of the restricted-product topology.

## Primality lemmas

`prime_natCast_ringOfIntegers` transports primality of `(p : ℤ)`
(`Nat.prime_iff_prime_int`) across the ring isomorphism
`Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ`, which sends `(p : ℤ)` to
`(p : 𝓞 ℚ)`. Hence `Ideal.span {(p : 𝓞 ℚ)}` is a nonzero prime ideal. In the
Dedekind domain `𝓞 ℚ` it is therefore maximal (`Ideal.IsPrime.isMaximal`). If a
finite place `v` contains `p`, then `span {p} ≤ v.asIdeal`. Since `v.asIdeal` is
proper, maximality forces equality; the converse is `Ideal.subset_span`. This
proves `natCast_mem_asIdeal_iff`. For `existsUnique_finitePlace_natCast_mem`, the
witness is the height-one prime `span {p}`. Uniqueness follows from the iff
lemma and `HeightOneSpectrum.ext`.

## Scope

This module does not prove a decomposition of the full finite adeles into a
`p`-factor times this ring, and does not compare residue scalars. It also makes no
comparison with `PrimeToProfiniteIntegerRing p` or with products indexed by
natural primes, and contains no Tate-module, Weil-group or monodromy construction.
Those comparisons are separate later statements. The module adds no hypotheses
beyond `p : ℕ` and, in the three primality lemmas, `p.Prime`.

## Provenance

The object is an internal restriction of the published full finite-adele model,
`FiniteAdeles ℚ` from `Langlands.Global.Adelic`, whose paired Markdown records
its sources. Implementation choices are internal and are not attributed to the
sources below:

- the index set as a subtype of `HeightOneSpectrum (𝓞 ℚ)` cut out by
  `(p : 𝓞 ℚ) ∉ v.asIdeal`;
- the use of Mathlib's `RestrictedProduct`;
- the explicit `p : ℕ` with no primality hypothesis in the construction.

Original sources for the mathematical object:

- André Weil, *Basic Number Theory*, second edition, Springer, 1973
  (`weil-1973-basic-number-theory`, SHA256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`),
  Chapter IV, §1, printed pp.59–60 (PDF pp.76–77). Page 59 defines `k_A(P)` as
  the product of the `k_v` for `v ∈ P` and the compact `r_v` for `v ∉ P`. These
  are open subrings with componentwise operations, and `k_A` is their union.
  Page 60 forms, for a place `v`, the analogous union `k'_A(v)` over the other
  places, and remarks that any finite set `P_0` of places may be split off in the
  same way. `PrimeToFiniteAdeles p` for prime `p` is this construction for
  `k = ℚ` with `P_0` consisting of the infinite place and the place of `p`. The
  page 60 canonical injection `x_v = ξ` at every `v` is the diagonal. The integral
  subring is the product of the `r_v` over the retained places. The product
  decomposition `k_A ≅ k_v × k'_A(v)` on page 60 is not formalized here.
- M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties*, Annals of Mathematics Studies 151, Princeton, 2001
  (`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`;
  printed page = PDF page − 8). Chapter I, §1, printed p.20 (PDF p.28) writes
  `A_L = A_L^S × L_S`, where `A_L^S` denotes "the adeles away from `S`" for a
  finite set `S` of places of a number field `L`. For `L = ℚ` and
  `S = {∞, p}`, `PrimeToFiniteAdeles p` corresponds to `A_ℚ^S` in this
  notation. Printed p.18 (PDF p.26) defines the "away from `S`" Tate modules
  `T^S A`, with limit over integers coprime to `S`, and prime-to-`p` isogenies.
  This is the motivation for the prime-to-`p` scalar ring in parent task
  `74795b53-92ee-4f6e-b0d3-bd3533def420`. Harris–Taylor use no `HeightOneSpectrum`
  model, and the decomposition `A_L = A_L^S × L_S` is not formalized here.

Worker 300 read Weil pp.59–60 and Harris–Taylor printed pp.18–20 directly through
text extraction of the registered PDFs, with hashes verified.

The proofs are internal. They use Mathlib's `RestrictedProduct` API in
`Topology/Algebra/RestrictedProduct/{Basic,TopologicalSpace}.lean`,
`RingTheory/DedekindDomain/{AdicValuation,FiniteAdeleRing}.lean`, and
`NumberTheory/NumberField/Basic.lean` (`Rat.ringOfIntegersEquiv`). They also use
the published `Langlands.Global.IntegralFiniteAdeles`
(`integralFiniteAdeles`, `isCompact_adicCompletionIntegers`).
