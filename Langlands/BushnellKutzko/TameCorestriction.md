# Tame corestrictions

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Definition (1.3.3), printed p. 29
(PDF p. 41).

`TameCorestriction O K E V` is an additive map from `A = Module.End K V` to
`B = Module.End E V` satisfying the left and right `B`-module identities and
the defining image equality for every hereditary `O`-order normalized by `Eˣ`.
The inclusion of `B` in `A` is `LinearMap.restrictScalars K`. The inclusion of
`Eˣ` in `Aˣ` is the published `subfieldUnits K E V`.

The order-image condition quantifies all published `LatticeChain O K V`, using
their `order` and `stabilizer`. These are exactly the hereditary orders in the
lattice-chain presentation used by Task 7398. The target set is the preimage of
the order under the inclusion `B → A`, so it is `𝔄 ∩ B` as a subset of `B`.

For a local field `F`, take `O = 𝒪[F]` and `K = F`. The parameters are deliberately
more general: for strata in a centralizer over `E`, the same mechanism can use
`O = subfieldIntegers F E` and `K = E`, as in the published subfield-order
statement. The ring, field and vector space have independent universes.

Only the defining properties of (1.3.3) are structure fields. Existence,
uniqueness up to an integer-ring unit, and images of all radical powers are
separate, unproved assertions in `TameCorestrictionStatement`.
