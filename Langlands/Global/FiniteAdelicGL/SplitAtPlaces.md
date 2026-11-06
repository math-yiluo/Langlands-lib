# Splitting finite adelic general linear groups at finitely many places

This internal construction fixes a number field `K`, a natural number `n` and a
predicate `p` on the finite places of `K`. It splits the Library's finite
adelic matrix-unit group `FiniteAdelicGL K n` at the places satisfying `p`.
When `p` is decidable and only finitely many places satisfy it, the result is
an isomorphism of topological groups

`FiniteAdelicGL K n ≃ₜ* (Π v : {v // p v}, FiniteLocalGL K n v) × AwayRestrictedProduct K n p`.

Here `FiniteLocalGL K n v` is the published general linear group over the
completion at `v`. The second factor is the restricted product away from `p`.
Writing `S` for the set of places satisfying `p`, this is the familiar
decomposition `GL_n(A_f) = Π_{v ∈ S} GL_n(K_v) × GL_n(A_f^S)`.

## Definitions

- `AwayRestrictedProduct K n p` is Mathlib's cofinite restricted product
  `Πʳ v : {v // ¬ p v}, [FiniteLocalGL K n v, localIntegral K n v]`. Here
  `localIntegral` is the published compact open subgroup of matrices with
  integral entries and integral inverse. No finiteness or decidability is
  assumed for this definition.
- `awayIntegral K n p` is the open subgroup of away families lying in
  `localIntegral K n v` at every place `v` not satisfying `p`. Openness is
  Mathlib's `RestrictedProduct.isOpen_forall_mem`, applied to the open
  subgroups `localIntegral`. `mem_awayIntegral` unfolds membership.
- `splitAtPlaces K n p` assumes `[DecidablePred p]` and
  `[Finite {v // p v}]`. It is the composite of the published
  `restrictedProductEquiv K n` from `FiniteAdelicGL.RestrictedProduct` with
  `RestrictedProduct.splitFiniteContinuousMulEquiv` from
  `Langlands.Topology.RestrictedProductSplit`. The hypothesis needed by the
  latter is openness of each `localIntegral K n v`.

## Properties

- `splitAtPlaces_apply_fst` and `splitAtPlaces_apply_snd` say that both
  components of `splitAtPlaces K n p g` at a place `v` are the published
  `localProjection K n v g`. Both hold by definition.
- `localProjection_splitAtPlaces_symm_of_pos` and
  `localProjection_splitAtPlaces_symm_of_neg` say that the inverse assembles
  an adelic matrix with prescribed local components. If `p v` holds, the
  local projection at `v` of `(splitAtPlaces K n p).symm z` is `z.1 ⟨v, h⟩`.
  Otherwise it is `z.2 ⟨v, h⟩`. The proof rewrites the local projection as a
  coordinate of `restrictedProductEquiv`, cancels it against its inverse, and
  applies the coordinate lemmas of the splitting.
- `mem_standardIntegral_iff_splitAtPlaces` characterizes the published
  standard integral subgroup. A matrix lies in `standardIntegral K n` exactly
  when its components at the places satisfying `p` lie in `localIntegral`, and
  its away part lies in `awayIntegral K n p`. This follows from the published
  `mem_standardIntegral_iff_local` by a case split on `p v`.
- `map_standardIntegral_splitAtPlaces` states the subgroup identity
  `splitAtPlaces(standardIntegral K n) =
  (Π_{v ∈ S} localIntegral K n v) × awayIntegral K n p`.
  The first factor is Mathlib's `Subgroup.pi Set.univ` and the product is
  `Subgroup.prod`. One inclusion is the characterization above. For the other,
  take the preimage `(splitAtPlaces K n p).symm z` and apply the
  characterization to it.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Prop. 4.10 on printed p. 311, ends by letting the level
`K(N)^{ℓ,p}` away from `ℓ` and `p` vary, with `GG(A_f^{ℓ,p})`-equivariance. The product-level constructions of the separate module
`Langlands.Shimura.PartialLevelTower`, which is not imported here, are stated
for an abstract product of topological groups. This module supplies such a product decomposition for the
Library's finite adelic general linear group. Harris's passage is motivation
only; no statement from it is formalized here. Harris works with a unitary
similitude group, and this module treats only `GL_n` over the finite adeles
of `K`.

The construction is derived from the published modules `LocalFactor`,
`StandardIntegralStatement` and `RestrictedProduct` in
`Langlands.Global.FiniteAdelicGL`, and from
`Langlands.Topology.RestrictedProductSplit`. It introduces no new topology, no
arithmetic existence assumptions and no restriction on `n`, including `n = 0`.
It constructs no level tower, Shimura variety or cohomology.
