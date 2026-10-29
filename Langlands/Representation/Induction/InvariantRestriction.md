# Restriction of equivariant maps to invariants

Author: Worker 61. Built on the published
`Langlands.Representation.Induction.PermutationInvariants`
(`quotientMapOfLE_fiber_finite`, `invariantsEquivOfEquiv`,
`pullbackInvariant`, `permutationInvariantsLinearEquiv`) and, through it, on
`Langlands.Representation.Induction.PermutationModule` (`permutation`,
`permutation_single`, `permutationFinsuppEquiv`, `permutationEquiv`) and
`Langlands.Representation.Induction.Definitions` (`compactInduced`). From
Mathlib it uses the coset spaces and the map between them
(`Subgroup.quotientMapOfLE`, `Subgroup.quotientEquivProdOfLE`, `Quotient.out`,
`Subgroup.index`), coinvariants (`Representation.Coinvariants`,
`Representation.Coinvariants.mk`, `Representation.Coinvariants.lift`,
`Representation.Coinvariants.hom_ext`,
`Representation.Coinvariants.mk_self_apply`) and invariants
(`Representation.invariants`) of a normal subgroup as representations of the
quotient group (`Representation.quotientToCoinvariants`,
`Representation.quotientToInvariants`), intertwining maps and equivalences of
representations (`Representation.IntertwiningMap`, `Representation.Equiv`),
pushforward of finitely supported functions (`Finsupp.lmapDomain`), and, for
the pro-`p` index, open subgroups of compact groups
(`Subgroup.quotient_finite_of_isOpen`, `Subgroup.normalCore`,
`Subgroup.isOpen_of_isClosed_of_finiteIndex`, `OpenNormalSubgroup`) and
`p`-groups (`IsPGroup.iff_card`).

All new names are in the namespace `Langlands.Induction`. `R` is a
commutative ring and `M` an `R`-module.

## Conventions

`G ⧸ H` is Mathlib's quotient by the left cosets `x H`, on which `G` acts by
left multiplication. `permutation R G (G ⧸ H) M` is the published
representation of `G` on `G ⧸ H →₀ M` in which `g` moves the value at `x H`
to `g x H` (`permutation_single`). For a normal subgroup `K` of `G` and a
representation `ρ` of `G`, `Representation.quotientToInvariants ρ K` and
`Representation.quotientToCoinvariants ρ K` are Mathlib's representations of
`G ⧸ K` on the `K`-invariants and on the `K`-coinvariants of `ρ`. For a
representation `σ` of `G ⧸ K`, `σ.comp (QuotientGroup.mk' K)` is its
inflation to `G`. The index of `H` in `K` is `(H.subgroupOf K).index`, the
index of `H ∩ K` in `K` (`0` if it is infinite).

## Fibres of `G ⧸ H → G ⧸ K`

`H ≤ K` are subgroups of a group `G`, with `hHK : H ≤ K`.

- `quotientMapOfLEFiberEquiv hHK q`: the fibre of
  `Subgroup.quotientMapOfLE hHK : G ⧸ H → G ⧸ K` over `q` is in bijection
  with `K ⧸ H.subgroupOf K`. Mathlib's `Subgroup.quotientEquivProdOfLE hHK`
  identifies `G ⧸ H` with `(G ⧸ K) × (K ⧸ H.subgroupOf K)`, with first
  component `quotientMapOfLE hHK`; the bijection is the second component.
- `card_quotientMapOfLE_fiber hHK q`: each fibre has `Nat.card` equal to the
  index of `H` in `K`. No finiteness is assumed: if the index is infinite,
  both sides are `0`.

With `K` normal:

- `quotientMapOfLE_smul_of_mem hHK k x`: for `k ∈ K`, the images of `k x` and
  `x` in `G ⧸ K` agree. For `x = g H`, `(k g)⁻¹ g = g⁻¹ k⁻¹ g ∈ K`.
- `quotientMapOfLE_smul hHK g x`: `G ⧸ H → G ⧸ K` is `G`-equivariant, where
  `g` acts on the group `G ⧸ K` by left multiplication by its class.

## Coinvariants of the permutation module

`H ≤ K` with `K` normal; no finiteness hypothesis.

- `permutationCoinvariantsToQuotient R M hHK`: the pushforward of finitely
  supported functions along `G ⧸ H → G ⧸ K`. It is constant on `K`-orbits by
  `quotientMapOfLE_smul_of_mem`, so it is defined on the `K`-coinvariants of
  `permutation R G (G ⧸ H) M` (by `Representation.Coinvariants.lift`).
  `permutationCoinvariantsToQuotient_mk` states its value on the class of a
  function.
- `quotientToPermutationCoinvariants R M`: sends `ψ : G ⧸ K →₀ M` to the
  class of the pushforward of `ψ` along `q ↦ q.out H`, where `q.out` is the
  representative of `q` chosen by `Quotient.out`.
- `permutationCoinvariantsLinearEquiv hHK`: these two maps are inverse
  `R`-linear equivalences. Pushforward along `q ↦ q.out H` followed by
  pushforward along `G ⧸ H → G ⧸ K` is pushforward along the identity. In the
  other order, by linearity it suffices to treat `Finsupp.single (g H) m`; it
  is sent to the class of `Finsupp.single (g k H) m`, where `g K = (g k) K`
  is the choice made by `Quotient.out`, for some `k ∈ K`. Since
  `g k g⁻¹ ∈ K` moves `g H` to `g k H`, the two classes agree.
- `permutationCoinvariantsEquiv R M hHK`: this linear equivalence is an
  equivalence of representations of `G ⧸ K`, from
  `Representation.quotientToCoinvariants (permutation R G (G ⧸ H) M) K` to the
  permutation representation `permutation R (G ⧸ K) (G ⧸ K) M` of `G ⧸ K` on
  itself, by `quotientMapOfLE_smul`.
- `permutationCoinvariantsFreeEquiv R hHK I`: for a type `I`, with
  coefficients `I →₀ R`, followed by the published
  `permutationFinsuppEquiv R (G ⧸ K) (G ⧸ K) I`, it is an equivalence with
  Mathlib's free `R[G ⧸ K]`-module of rank `I`,
  `Representation.free R (G ⧸ K) I`.

## From invariants to coinvariants

`ρ` and `σ` are representations of `G` on `R`-modules `V` and `W`, and `K` is
normal.

- `invariantsToCoinvariants ρ K`: the inclusion of the `K`-invariants followed
  by the projection to the `K`-coinvariants, as an intertwining map from
  `Representation.quotientToInvariants ρ K` to
  `Representation.quotientToCoinvariants ρ K`.
  `invariantsToCoinvariants_apply` states that an invariant vector goes to its
  class.
- `coinvariantsEquivOfEquiv K e`: an equivalence `e` of representations of `G`
  induces an equivalence of the representations of `G ⧸ K` on
  `K`-coinvariants: `e` and `e.symm`, followed by the projection, are constant
  on `K`-orbits because they are equivariant, so they factor through the
  coinvariants of the source.
- `invariantsToCoinvariants_equiv K e v`: `invariantsToCoinvariants` commutes
  with the published `invariantsEquivOfEquiv K e` on invariants and
  `coinvariantsEquivOfEquiv K e` on coinvariants (by definition).
- `bijective_invariantsToCoinvariants_of_equiv K e h`: hence if
  `invariantsToCoinvariants σ K` is bijective and `ρ` is equivalent to `σ`,
  then `invariantsToCoinvariants ρ K` is bijective.

## The permutation module: multiplication by the index

`H ≤ K`, `K` normal and `H` of finite index in `K`.

- `permutationCoinvariantsLinearEquiv_invariantsToCoinvariants hHK ψ`: for
  `ψ : G ⧸ K →₀ M`, `invariantsToCoinvariants` applied to the invariant
  function `pullbackInvariant R hHK ψ` (`g H ↦ ψ (g K)`) and followed by
  `permutationCoinvariantsLinearEquiv` is `(H.subgroupOf K).index • ψ`. The
  map is the pushforward along `G ⧸ H → G ⧸ K`. Its value at `q` is the sum
  of `ψ q` over the points of the fibre over `q` in the support of the
  pullback. If `ψ q ≠ 0` these are all the points of the fibre, which is
  finite (`quotientMapOfLE_fiber_finite`), and their number is the index
  (`card_quotientMapOfLE_fiber`).
- `bijective_invariantsToCoinvariants_permutation hHK h`: if the index, cast
  to `R`, is a unit (`h`), then `invariantsToCoinvariants` is bijective for
  `permutation R G (G ⧸ H) M`. Up to the linear equivalences
  `permutationInvariantsLinearEquiv R M hHK` and
  `permutationCoinvariantsLinearEquiv hHK`, it is multiplication by the unit
  index.

## Restriction to invariants

`ρ` is a representation of `G` on `V`, `K` is normal, and `σ` is a
representation of `G ⧸ K` on `W`.

- `homCoinvariantsEquiv ρ K σ`: an `R`-linear equivalence between
  intertwining maps from `ρ` to the inflation `σ.comp (QuotientGroup.mk' K)`
  and intertwining maps from `Representation.quotientToCoinvariants ρ K` to
  `σ`. A `G`-map `f` is constant on `K`-orbits, because `K` acts trivially on
  the inflation, so it factors through the coinvariants; conversely a map on
  coinvariants is composed with the projection.
- `invariantsRestriction ρ K σ`: the `R`-linear map restricting a `G`-map
  `f : ρ → σ.comp (QuotientGroup.mk' K)` to the `K`-invariants of `ρ`, as an
  intertwining map from `Representation.quotientToInvariants ρ K` to `σ`.
  `invariantsRestriction_apply` states its values.
- `invariantsRestriction_eq_comp f`: `invariantsRestriction ρ K σ f` is
  `homCoinvariantsEquiv ρ K σ f` composed with `invariantsToCoinvariants ρ K`.
- `precompEquiv τ e`: for an equivalence `e : α ≃ β` of representations of a
  group `G'` and a representation `τ` of `G'`, composition with `e` is an
  `R`-linear equivalence from intertwining maps `β → τ` to intertwining maps
  `α → τ`, with inverse composition with `e.symm`. The Library has the same
  construction as the private `homPrecompEquiv` in
  `Langlands.Representation.Classification.HeadHomMultiplicityProof`, over
  `ℂ` only; being private, it cannot be reused.
- `invariantsRestrictionEquiv ρ K σ h`: if `invariantsToCoinvariants ρ K` is
  bijective (`h`), restriction to the `K`-invariants is an `R`-linear
  equivalence. It is `homCoinvariantsEquiv` followed by `precompEquiv` along
  the equivalence of representations of `G ⧸ K` given by
  `invariantsToCoinvariants ρ K` (Mathlib's
  `Representation.IntertwiningMap.ofBijective`).
  `invariantsRestrictionEquiv_apply` states that its underlying map is
  `invariantsRestriction`.

## Pro-`p` index

`G` is a topological group, `p` a prime, `H` an open subgroup of `G`, and `K`
a subgroup that is compact in the subspace topology (`[CompactSpace K]`) and
whose quotients by all open normal subgroups are `p`-groups (`hK`). These are
the fields `compactSpace` and `isPGroup` of the published
`Langlands.Cohomology.IsProPSubgroup p K` (in
`Langlands.Cohomology.DivisibleSystem.ProPInvariants`); `hp` is its field
`prime`. The structure is not imported, to keep this module free of the
cohomology modules.

- `exists_index_subgroupOf_eq_pow hp hH hK`: the index of `H` in `K` is a
  power of `p`. `H ∩ K` is open in `K`, hence of finite index since `K` is
  compact. Its normal core `N` in `K` is closed and of finite index, hence
  open, so `K ⧸ N` is a finite `p`-group of order `p ^ n`, and the index of
  `H ∩ K` divides the index `p ^ n` of `N`.
- `isUnit_index_subgroupOf hp hR hH hK`: if `p` is a unit of `R` (`hR`), so
  is the index of `H` in `K`.

`H ≤ K` is not needed here.

## Compact induction of trivial representations

`G` is a topological group, `hH : IsOpen (H : Set G)`, `hHK : H ≤ K` and `K`
is normal.

- `compactInducedCoinvariantsEquiv R M hH hHK`: the `K`-coinvariants of the
  published compact induction
  `compactInduced H (Representation.trivial R H M)`, as a representation of
  `G ⧸ K`, are equivalent to `permutation R (G ⧸ K) (G ⧸ K) M`:
  `coinvariantsEquivOfEquiv` of the published `permutationEquiv R M H hH`,
  followed by `permutationCoinvariantsEquiv`.

In addition `H` has finite index in `K`.

- `bijective_invariantsToCoinvariants_compactInduced hH hHK h`: if the index
  is a unit of `R`, `invariantsToCoinvariants` is bijective for this compact
  induction, by `bijective_invariantsToCoinvariants_of_equiv` and
  `bijective_invariantsToCoinvariants_permutation`.
- `compactInducedInvariantsRestrictionEquiv hH hHK σ h`: for a representation
  `σ` of `G ⧸ K` and the index a unit of `R`, restriction to `K`-invariants
  is an `R`-linear equivalence from the `G`-maps out of
  `compactInduced H (Representation.trivial R H M)` into the inflation of
  `σ` to the `G ⧸ K`-maps from its `K`-invariants to `σ`
  (`invariantsRestrictionEquiv`).

With `K` compact and pro-`p` and `p` a unit of `R`, the finite-index and unit
hypotheses are supplied by the published
`finiteIndex_subgroupOf_of_isCompact` (from `IsCompact (K : Set G)`) and by
`isUnit_index_subgroupOf`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10 (Worker 61 read
the rendered scanned pages):

- printed p.305 (one-based PDF page 7), §2: "Since `p` is prime to `ℓ`, the
  functor `H⁰(H, •)` is exact on `ℓ`-primary torsion modules", for an open
  normal pro-`p` subgroup `H ⊂ S(ẽ)`;
- printed p.310 (one-based PDF page 12): "Let `H_p` be an open normal pro-`p`
  subgroup of `C_p` contained in `K_p`";
- printed p.311 (one-based PDF page 13): the complexes are rewritten as
  (4.10.2), a sum of the modules
  `Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ), Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`; "Up to
  conjugacy, we may assume `S(ẽ) ⊂ C_p`"; and "`C^j(ẽ)` has been chosen to
  be a direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies
  over a family of open subgroups of `S(ẽ)`";
- printed p.312 (one-based PDF page 14): "We may replace `C^j_m(ẽ)` by
  `C^j_m(ẽ)^{H_p}` in (4.10.2)", followed by the definition
  `T_m(j, ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`.

Harris gives no argument for the replacement. Our reading is: the target
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` is a representation of `S(ẽ) ⧸ H_p`, so a map
from `C^j_m(ẽ)` into it factors through the `H_p`-coinvariants
(`homCoinvariantsEquiv`). For a free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-module with
`H(ẽ) ⊆ H_p`, the map from `H_p`-invariants to `H_p`-coinvariants is
multiplication by a power of `p`, which is invertible in `𝒪/ℓ^m𝒪` since
`p` is prime to `ℓ`. Then the restriction to invariants is an isomorphism
(`invariantsRestrictionEquiv`). In this reading `G`, `H` and `R` correspond
to `S(ẽ)`, `H(ẽ)` and `𝒪/ℓ^m𝒪`, and `K` to `H_p`, more precisely to
`H_p ∩ S(ẽ)`, which is normal in `S(ẽ)` because `S(ẽ) ⊂ C_p` and `H_p` is
normal in `C_p`. The correspondence, the assumption `H(ẽ) ⊆ H_p`, and the
hypotheses of this module (normality of `K`, `H` open, the index a unit)
are our interpretation, not statements quoted from the source.

The module is derived: the comparison of invariants and coinvariants of
permutation modules and the coinvariants/inflation adjunction are standard,
and all definitions and proofs are ours.

## Scope

The module does not treat Harris's modules `C^j_m(ẽ)`, which are direct
limits of free modules, and does not prove that `invariantsToCoinvariants` is
bijective for them; direct limits are not treated at all. It does not
connect `T_m(j, ẽ)` or the complexes (4.10.2) to the Library's objects, and
it does not derive the Mittag-Leffler condition or the surjectivity of
(4.10.3). Coinvariants and invariants are compared only for permutation
modules, that is, for compact inductions of trivial representations. The
equivalences are of `R`-modules of intertwining maps; no adjunction of
functors between categories of representations is constructed.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
