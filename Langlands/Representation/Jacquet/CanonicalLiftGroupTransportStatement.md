# Canonical Jacquet lift transport through continuous group equivalences

Author: Worker 127.

This module states internal naturality assertions for the published compact
averages and canonical-lift constructions. All five declarations are
Prop-valued definitions in `Langlands.Jacquet`; none proves an assertion.
The module introduces no carrier, action, quotient, or linear map.

## Parameters and subgroup convention

Every clause has independent universes `uG`, `uH`, and `uV` for groups `G`, `H`
and the complex module `V`. Both groups have arbitrary `Group`,
`TopologicalSpace`, and `IsTopologicalGroup` instances. The carrier `V` has only
`AddCommGroup` and `Module ℂ` instances; no topology on `V` is required.
The group and carrier parameters are implicit, so the bundled proposition is
used as `CanonicalLiftGroupTransportStatement (G := G) (H := H) (V := V)`.

Each clause universally quantifies a continuous group equivalence
`e : H ≃ₜ* G`, a representation `ρ : Representation ℂ G V`, its smoothness
proof `hρ`, compact open subgroups `K : OpenSubgroup H` and
`L : OpenSubgroup G`, and their compactness proofs `hK` and `hL`.
The exact subgroup hypothesis is the forward image equality

```lean
K.toSubgroup.map e.toMonoidHom = L.toSubgroup
```

The source representation is always the actual same-carrier pullback
`ρ.comp e.toMonoidHom`, with smoothness supplied by the existing theorem
`isSmooth_comp e.toMonoidHom e.continuous hρ`. No independently chosen
representation or transport map is supplied.

## The four clauses

`CanonicalLiftAverageGroupTransportClause` states equality of the normalized
averages as complex linear endomorphisms of the same `V`:

```lean
Compact.averageMap (ρ.comp e.toMonoidHom)
  (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK =
Compact.averageMap ρ hρ L hL
```

`CanonicalLiftStableImageGroupTransportClause` further quantifies every
`g : H`, every `v : V`, and proofs that `v` lies in both corresponding
fixed-vector submodules. It asserts that `⟨v, hvK⟩` lies in the pulled-back
`stableImage` at `K, g` if and only if `⟨v, hvL⟩` lies in the target
`stableImage` at `L, e g`. These are the existing intersections of the ranges
of all natural powers of the compressed actions, including power zero.
The assertion uses fixed-vector subtypes of the same ambient vector and
introduces no replacement stable-image carrier. Supplying both fixedness
proofs makes the formula directly usable without a cast; the actual image
identity also identifies the two ambient fixed submodules.

`CanonicalLiftPowerKernelGroupTransportClause` further quantifies every
`g : H`, `N M : Subgroup H`, `N' M' : Subgroup G`, and normalizer inclusions
`hMN : M ≤ Subgroup.normalizer N` and
`hM'N' : M' ≤ Subgroup.normalizer N'`. Its remaining hypotheses are exactly

```lean
N.map e.toMonoidHom = N'
M.map e.toMonoidHom = M'
```

It states that the equality of submodules of the source fixed-vector space

```lean
powerKernelSup (ρ.comp e.toMonoidHom)
  (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g =
LinearMap.ker (fixedJacquetMap (ρ.comp e.toMonoidHom) N M hMN K.toSubgroup)
```

holds if and only if the corresponding target equality holds with
`ρ, hρ, L, hL, e g, N', M', hM'N'`. Each side of the equivalence is an equality
in its own existing fixed-vector space. Neither equality is a hypothesis.
The `powerKernelSup` is the actual submodule supremum of the kernels of
all powers of the published compressed action.

`CanonicalLiftBijectiveGroupTransportClause` has the same hypotheses as the
kernel clause. It asserts an equivalence between `Function.Bijective` of the
actual `stableImageJacquetMap` on the pulled-back data and
`Function.Bijective` of that actual map on the target data. The maps restrict
the original Jacquet quotient maps, and their codomains are exactly

```lean
fixedVectors (action (ρ.comp e.toMonoidHom) N M hMN)
  (K.toSubgroup.comap M.subtype)
fixedVectors (action ρ N' M' hM'N')
  (L.toSubgroup.comap M'.subtype)
```

These use the unnormalized descended actions and the actual subgroups
`K ∩ M` inside `M` and `L ∩ M'` inside `M'`. Thus the assertion concerns
bijectivity onto the required fixed Jacquet quotients, not an abstract
substitute map. Neither bijectivity is assumed.

`CanonicalLiftGroupTransportStatement` is the conjunction in this order:
average equality, stable-image membership transport, kernel-identification
transport, and quotient-bijectivity transport. For a proof `h` of the bundled
proposition the clauses are `h.1`, `h.2.1`, `h.2.2.1`, and `h.2.2.2`.
There are no finite-dimensionality, admissibility, nilpotence, canonical-lift,
parabolic-shape, smooth-dual, or pairing hypotheses. No smooth-dual or pairing
conclusion is stated. The zero module and arbitrary group elements and
subgroup pairs remain allowed.

## Derived provenance and proof obligations

These statements are derived functoriality of existing Library definitions,
not quotations from external literature. Their dependencies are
`Langlands.Representation.Jacquet.CanonicalLiftDefinitions`,
`Langlands.Representation.CuspidalSupport.GroupTransport`, and the compact
averaging and smooth pullback modules imported by them.

The intended mathematical justification is equality of the actual subgroup
orbits in `V`, hence equality of the normalized `orbitMean` averages;
identification of the fixed submodules, hence conjugacy of the compressed
actions and every power; and transport of the actual Jacquet quotients.
The existing `fixedVectors_comp_mulEquiv` writes the corresponding fixed
submodule using inverse comap, which agrees with forward image for the
equivalence. Existing `Jacquet.coinvariantsMapEquiv` and its evaluation law
`coinvariantsMapEquiv_mk` give the quotient identification, sending the
class of `v` to the class of `v` at the image of `N`.

A proof must also show that this quotient identification transports the
unnormalized `M` action to the `M'` action and identifies their respective
`K ∩ M` and `L ∩ M'` fixed spaces. It can then compare the actual restricted
maps, transfer their kernels and bijectivity, and transfer membership in
every power range. This is a proof plan explaining the internal provenance;
none of these transport results is proved or assumed by this statement module.
