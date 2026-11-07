# Splitting the finite adeles at finitely many places

Author: Worker 13.

This internal construction fixes a number field `K` and a predicate `p` on the
finite places of `K`. When `p` is decidable and only finitely many places
satisfy it, it identifies the published finite adeles `FiniteAdeles K` (from
`Langlands.Global.Adelic`) with a product of topological rings

`FiniteAdeles K ≃+* (Π v : {v // p v}, FiniteCompletion K v.1) × AwayFiniteAdeles K p`.

The first factor is the full product of the completions at the places
satisfying `p`. The second is the finite adeles away from those places. Writing
`S` for the set of places satisfying `p`, this is the decomposition
`A_f = K_S × A_f^S` with `K_S = Π_{v ∈ S} K_v`. The splitting carries the
published integral finite adeles onto the product of the local integer rings at
`S` and the away integral subring. For `K = ℚ` and the places whose prime ideal
contains a nonzero natural number `n`, the second factor is, by definition, the
published `PrimeToFiniteAdeles n`. In that case the splitting is an isomorphism
of topological `ℚ`-algebras.

## Restricted products of rings

These declarations are in namespace `RestrictedProduct`. They take an index type
`ι`, rings `R i` and subrings `B i` (any `SubringClass`). The restricted
product is Mathlib's `Πʳ i, [R i, B i]` relative to the cofinite filter.

- `finiteRingEquiv R B` assumes `[Finite ι]`. It is the ring isomorphism
  `Πʳ i, [R i, B i] ≃+* Π i, R i` that forgets the restriction. The inverse
  uses `cofinite_eq_bot`: over a finite index type every family satisfies the
  restriction. `finiteRingEquiv_apply` and `finiteRingEquiv_symm_apply` give
  its coordinates; both hold by definition.
- `splitRingEquiv R B p` assumes `[DecidablePred p]`. It is the ring
  isomorphism
  `Πʳ i, [R i, B i] ≃+* Πʳ (i : {i // p i}), [R i, B i] × Πʳ (i : {i // ¬ p i}), [R i, B i]`.
  Its underlying equivalence is the published `splitEquiv` of
  `Langlands.Topology.RestrictedProductSplit`, applied to the carriers of the
  `B i`. Addition and multiplication are preserved by definition, since both
  sides use coordinatewise operations. `splitRingEquiv_apply_fst` and
  `splitRingEquiv_apply_snd` give the two restrictions. `splitRingEquiv_symm_apply`
  says that the inverse is the published `glueSubtype`.
- `splitFiniteRingEquiv R B p` also assumes `[Finite {i // p i}]`. It composes
  `splitRingEquiv` with `finiteRingEquiv` on the first factor, giving
  `Πʳ i, [R i, B i] ≃+* (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i]`.
  `splitFiniteRingEquiv_apply_fst` and `splitFiniteRingEquiv_apply_snd` give
  the coordinates of the image. `splitFiniteRingEquiv_symm_apply_of_pos` and
  `splitFiniteRingEquiv_symm_apply_of_neg` give the coordinate of the inverse
  at `i`: it is `z.1 ⟨i, h⟩` when `h : p i` and `z.2 ⟨i, h⟩` when
  `h : ¬ p i`. They follow from the published `glueSubtype_apply_of_pos` and
  `glueSubtype_apply_of_neg`.
- `coe_splitFiniteRingEquiv` and `coe_splitFiniteRingEquiv_symm` assume
  topologies on the `R i` and openness of every `B i`. They say that
  `splitFiniteRingEquiv R B p` and its inverse have the same underlying
  functions as the published homeomorphism `splitFiniteHomeomorph R p hB` and
  its inverse. Both hold by definition.

## Finite adeles away from `p`

These declarations are in namespace `Langlands.Global`. They take a number
field `K` and any predicate `p : FinitePlace K → Prop`. No decidability or
finiteness is assumed until the splitting itself.

- `AwayFiniteAdeles K p` is an `abbrev` for Mathlib's restricted product
  `Πʳ v : {v : FinitePlace K // ¬ p v}, [FiniteCompletion K v.1, v.1.adicCompletionIntegers K]`
  relative to the cofinite filter. Its ring operations are coordinatewise and
  its topology is Mathlib's restricted-product topology.
- The instance `IsTopologicalRing (AwayFiniteAdeles K p)` is Mathlib's
  `RestrictedProduct.isTopologicalRing`. It is applied with the openness of
  every local completed-integer ring (`Valued.isOpen_valuationSubring`), as for
  the published `PrimeToFiniteAdeles`.
- `awayRestriction K p : FiniteAdeles K →+* AwayFiniteAdeles K p` restricts a
  finite adele to the places not satisfying `p`.
  `awayRestriction_apply` says that its coordinate at `v` is `a v.1`. The
  restriction condition is transported along the injective inclusion of the
  subtype, which maps the cofinite filter into the cofinite filter.
  `continuous_awayRestriction` is Mathlib's
  `RestrictedProduct.mapAlong_continuous`.
- `awayDiagonal K p : K →+* AwayFiniteAdeles K p` is the composite of
  `awayRestriction K p` with the diagonal `algebraMap K (FiniteAdeles K)`.
  `awayDiagonal_apply` says that its coordinate at `v` is
  `algebraMap K (FiniteCompletion K v.1) x`. The module deliberately declares no
  `Algebra K (AwayFiniteAdeles K p)` instance. For `K = ℚ` such an instance
  would be a second `ℚ`-algebra structure on `PrimeToFiniteAdeles n`, besides
  the published one.
- `awayIntegralFiniteAdeles K p` is the subring of away families whose
  coordinate lies in `v.1.adicCompletionIntegers K` at every place `v` not
  satisfying `p`. `mem_awayIntegralFiniteAdeles` unfolds membership.
  `isOpen_awayIntegralFiniteAdeles` is Mathlib's
  `RestrictedProduct.isOpen_forall_mem`, so openness is in the actual
  restricted-product topology. `isCompact_awayIntegralFiniteAdeles` says that the
  subring is compact. It is the range of Mathlib's structure map from the full
  product of the local integer rings
  (`RestrictedProduct.range_structureMap`). That map is continuous, and its
  source is compact by Tychonoff and the published
  `isCompact_adicCompletionIntegers`.
- `localIntegralProduct K p` is the subring of families
  `x : Π v : {v // p v}, FiniteCompletion K v.1` with every coordinate in
  `v.1.adicCompletionIntegers K`. `mem_localIntegralProduct` unfolds membership.
  `isCompact_localIntegralProduct` is Tychonoff (`isCompact_univ_pi`) applied
  to the published compactness of the local integer rings.
  `isOpen_localIntegralProduct` assumes `[Finite {v // p v}]` and uses
  `isOpen_set_pi` for a finite product of open sets.
- `finite_mem_asIdeal K a ha` says that for `a : 𝓞 K` with `a ≠ 0`, only
  finitely many finite places have prime ideal containing `a`. Such a prime
  divides the nonzero ideal `Ideal.span {a}`, and Mathlib's
  `Ideal.finite_factors` says that a nonzero ideal has only finitely many
  height-one prime factors. `finite_natCast_mem_asIdeal K n hn` is the case
  `a = (n : 𝓞 K)` for a natural number `n ≠ 0`.

## The splitting

From here on `[DecidablePred p]` and `[Finite {v : FinitePlace K // p v}]` are
assumed.

- `finiteAdelesSplit K p` is the ring isomorphism
  `FiniteAdeles K ≃+* (Π v : {v // p v}, FiniteCompletion K v.1) × AwayFiniteAdeles K p`.
  It is `RestrictedProduct.splitFiniteRingEquiv` applied to the completions
  `FiniteCompletion K v` and their integer rings `v.adicCompletionIntegers K`.
  This uses that `FiniteAdeles K` is, by definition, Mathlib's
  `FiniteAdeleRing (𝓞 K) K`, the cofinite restricted product of exactly these
  completions and integer rings.
- `finiteAdelesSplit_apply_fst` says that the first component at `v` is `a v.1`.
  `finiteAdelesSplit_apply_snd` says that the second component is
  `awayRestriction K p a`. `finiteAdelesSplit_symm_apply_of_pos` and
  `finiteAdelesSplit_symm_apply_of_neg` give the coordinate at `v` of the
  inverse: `z.1 ⟨v, h⟩` if `h : p v` and `z.2 ⟨v, h⟩` if `h : ¬ p v`.
- `finiteAdelesSplitHomeomorph K p` is the same splitting as a homeomorphism for
  the restricted-product topologies. It is the published
  `RestrictedProduct.splitFiniteHomeomorph`, applied with the openness of every
  local integer ring. `coe_finiteAdelesSplitHomeomorph` and
  `coe_finiteAdelesSplitHomeomorph_symm` say that it and its inverse have the
  same underlying functions as `finiteAdelesSplit K p` and its inverse.
  `continuous_finiteAdelesSplit` and `continuous_finiteAdelesSplit_symm` follow.
  So `finiteAdelesSplit K p` is an isomorphism of topological rings, where the
  target carries the product of the product topology and the restricted-product
  topology.
- `finiteAdelesSplit_algebraMap` says that the diagonal image of `x : K` goes to
  the pair of the local images `algebraMap K (FiniteCompletion K v.1) x` at the
  places satisfying `p` and the away diagonal image `awayDiagonal K p x`.

## Integral finite adeles

- `mem_integralFiniteAdeles_iff_finiteAdelesSplit` says that a finite adele lies
  in the published `integralFiniteAdeles K` exactly when the first component of
  its splitting lies in `localIntegralProduct K p` and the second lies in
  `awayIntegralFiniteAdeles K p`. The proof applies the published
  `mem_integralFiniteAdeles` and splits on `p v`.
- `map_integralFiniteAdeles_finiteAdelesSplit` states the subring identity
  `finiteAdelesSplit K p (integralFiniteAdeles K) =
  localIntegralProduct K p × awayIntegralFiniteAdeles K p`, with Mathlib's
  `Subring.map` and `Subring.prod`. One inclusion is the characterization
  above. For the other, take the preimage under the inverse and apply the
  characterization to it.
- `integralFiniteAdelesSplit K p` is the resulting ring isomorphism
  `integralFiniteAdeles K ≃+* localIntegralProduct K p × awayIntegralFiniteAdeles K p`.
  It composes `RingEquiv.subringMap`, `RingEquiv.subringCongr` for the subring
  identity, and `Subring.prodEquiv`. `coe_integralFiniteAdelesSplit_fst` and
  `coe_integralFiniteAdelesSplit_snd` say that its components are the
  components of `finiteAdelesSplit K p`.

## The rational case

Take `K = ℚ`, a natural number `n` and the predicate
`fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal`. Its complement is the predicate defining the
published index set `PrimeToFinitePlace n`, so the following hold by
definition (`rfl`) for every `n`:

- `awayFiniteAdeles_natCast n`:
  `AwayFiniteAdeles ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) = PrimeToFiniteAdeles n`.
- `awayRestriction_natCast n`: `awayRestriction` is the ring map underlying the
  published `primeToFiniteRestriction n`.
- `awayDiagonal_natCast n`: `awayDiagonal` is the published `primeToDiagonal n`.
- `awayIntegralFiniteAdeles_natCast n`: `awayIntegralFiniteAdeles` is the
  published `primeToIntegralFiniteAdeles n`.

For `hn : n ≠ 0`, `finite_natCast_mem_asIdeal` gives the finiteness hypothesis.
Decidability of the predicate is supplied classically.

- `ratFiniteAdelesSplit n hn` is the isomorphism of topological `ℚ`-algebras
  `FiniteAdeles ℚ ≃A[ℚ] (Π v : {v // (n : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ v.1) × PrimeToFiniteAdeles n`.
  Its ring isomorphism is `finiteAdelesSplit`, and continuity in both directions
  is `continuous_finiteAdelesSplit` and `continuous_finiteAdelesSplit_symm`. The
  target carries the product `ℚ`-algebra structure: the completions'
  `ℚ`-algebra structures on the first factor and the published diagonal
  `ℚ`-algebra structure of `PrimeToFiniteAdeles n` on the second.
  Compatibility with `algebraMap` holds by definition.
- `ratFiniteAdelesSplit_apply_fst` and `ratFiniteAdelesSplit_apply_snd` give the
  components. The second component of `a` is `primeToFiniteRestriction n a`.
  `snd_comp_ratFiniteAdelesSplit` states the same as an identity of continuous
  `ℚ`-algebra maps: the second projection composed with the splitting is
  `primeToFiniteRestriction n`.
- `ratFiniteAdelesSplit_symm_apply_of_mem` and
  `ratFiniteAdelesSplit_symm_apply_of_not_mem` give the coordinates of the
  inverse.
- `mem_integralFiniteAdeles_iff_ratFiniteAdelesSplit` says that a rational
  finite adele is integral exactly when its components at the places containing
  `n` are integral and its prime-to-`n` part lies in
  `primeToIntegralFiniteAdeles n`.

For prime `n`, the published `existsUnique_finitePlace_natCast_mem` shows that
the first factor is indexed by the single place whose prime ideal is `(n)`.
This module does not identify that place or its completion with `ℚ_n`.

## Sources and provenance

The construction is internal. It is derived from Mathlib's `RestrictedProduct`
API, `Ideal.finite_factors`, `isCompact_univ_pi` and `isOpen_set_pi`. It also
uses the published `Langlands.Topology.RestrictedProductSplit` (`splitEquiv`,
`glueSubtype`, `splitFiniteHomeomorph`), `Langlands.Global.Adelic`,
`Langlands.Global.IntegralFiniteAdeles` (`integralFiniteAdeles`,
`isCompact_adicCompletionIntegers`) and `Langlands.Global.PrimeToFiniteAdeles`.
The predicate formulation, the subtype indexing and the absence of an
`Algebra K` instance on `AwayFiniteAdeles K p` are implementation choices, not
attributed to the sources below.

The mathematical decomposition is classical:

- André Weil, *Basic Number Theory*, second edition, Springer, 1973
  (`weil-1973-basic-number-theory`), Chapter IV, §1, printed pp.59–60 (PDF
  pp.76–77). Page 59 defines `k_A(P) = Π_{v ∈ P} k_v × Π_{v ∉ P} r_v` and the
  adele ring as their union, with each `k_A(P)` an open subring. Page 60
  writes `k_A(P)` for `P ∋ v` as `k_v` times an infinite product `k'_A(P, v)`.
  The union of the `k'_A(P, v)` is a locally compact ring `k'_A(v)`, and `k_A`
  is isomorphic to `k_v × k'_A(v)`. Weil then remarks that "instead of one
  place v of k, one could start with any finite set P_0 of such places so as
  to write k_A as the product of the fields k_v for v ∈ P_0 and of one more
  factor". `finiteAdelesSplit` is this statement for the finite adeles, with
  `P_0` the finite set of finite places satisfying `p`. `AwayFiniteAdeles K p`
  is the extra factor. Weil works with the full adele ring including the
  infinite places, whereas this module works only with the finite adeles.
- M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties*, Annals of Mathematics Studies 151, Princeton, 2001
  (`harris-taylor-2001-geometry-cohomology-simple-shimura`), Chapter I, printed
  p.20 (PDF p.28): "If S is a finite set of places of L we decompose
  A_L = A_L^S × L_S where A_L^S denotes the adeles away from S and where
  L_S = Π_{x ∈ S} L_x". Restricted to finite places, `AwayFiniteAdeles K p`
  corresponds to the finite part of `A_L^S` and the first factor to `L_S`.

Worker 13 read Weil printed pp.59–60 and Harris–Taylor printed p.20 through
text extraction of the registered PDFs.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on GL(n)*,
Prop. 4.10 on printed p.311, lets the level `K(N)^{ℓ,p}` away from `ℓ` and `p`
vary, with `GG(A_f^{ℓ,p})`-equivariance. The groups `A_f^{ℓ,p}` there are
finite adeles away from finitely many places, which this module provides for
the base ring. Harris's passage is motivation only; no statement from it is
formalized here.

The module splits only the ring of finite adeles. It does not split any adelic
group of points, does not treat the infinite places, and constructs no level
tower, Shimura variety or cohomology. The integral correspondence and the
rational identification with `PrimeToFiniteAdeles n` are stated explicitly
above. No arithmetic hypothesis beyond the finiteness and decidability of `p`
is assumed, and in the rational case only `n ≠ 0`.
