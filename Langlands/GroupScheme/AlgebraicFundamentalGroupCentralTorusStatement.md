# Exactness of algebraic fundamental groups for a central torus quotient

This module states the exact sequence of algebraic fundamental groups attached
to a quotient of a connected reductive group by a central torus. The source is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- §11.5, printed p. 429 / PDF p. 460: for a z-extension
  `1 → Z → G̃ → G → 1`, “the maps `G̃(K) → G(K)` and `π₁(G̃) → π₁(G)` are
  surjective”;
- proof of Lemma 11.5.1, printed p. 430 / PDF p. 461: for a maximal torus
  `T ⊂ G` with preimage `T̃ ⊂ G̃`, “the coroot lattice `Q^∨ ⊂ X_*(T̃)` has
  trivial intersection with `X_*(Z)`, which leads to the exact sequence
  `0 → π₁(Z) → π₁(G̃) → π₁(G) → 1`”.

The authors' corrections of 1 November 2024 have no entries for §§11.4–11.5.

## The statement

`CentralTorusFundamentalExactnessStatement` quantifies over every field `k`,
every separable closure `E` of `k` (`IsSepClosure k E`), every `k`-torus `Z`
(`IsTorus Z.toGrp`, an actual torus scheme), all connected reductive
`k`-groups `H` and `G`, and actual homomorphisms `i : Z → H` and `p : H → G`
such that

- `i` is a closed subgroup (`IsClosedSubgroup i`, a closed immersion);
- `i` is central (`IsCentral i`: every point of `Z` maps into the centre of
  `H` on every test scheme);
- `p` is the represented fppf quotient by the full subgroup functor of `Z`
  (`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p`: `p` is flat,
  surjective and locally of finite presentation, and its actual scheme kernel
  has exactly the points of the image of `i` on every test scheme).

It asserts, for the maps `fundamentalGroupMap` already defined in
`Langlands.GroupScheme.AlgebraicFundamentalGroupFunctor`:

1. the map `π₁(Z) → π₁(H)` induced by `i` is injective;
2. the map `π₁(H) → π₁(G)` induced by `p` is surjective;
3. the range of the first map equals the kernel of the second.

Together these say that `0 → π₁(Z) → π₁(H) → π₁(G) → 0` is exact. Here
`π₁(Z)` is the Library's `fundamentalGroup` of the torus `Z`, using the
published proof `IsTorus.isConnectedReductive_of_fieldSplitting` that a torus
is connected reductive. All groups are the chosen presentations
`X_*(T)/X_*(T_sc)` of KP Construction 11.3.1 over `E`, and the maps are the
actual selected maps characterized by geometric torus factorizations. No
induced map, exactness, surjectivity, chosen lift or other witness is a
hypothesis. Existence and uniqueness of the selected maps are the separate
obligations `AlgebraicFundamentalGroupMapStatement`, which this statement
neither assumes nor changes.

## Provenance and scope

KP states the sequence for z-extensions, where `Z` is an induced torus and the
derived subgroup of `G̃` is simply connected. This statement is a derived
generalization to an arbitrary central torus: it keeps every characteristic
and does not require `Z` to be induced or the derived subgroup to be simply
connected. The generalization is the same coroot-lattice argument. A maximal
torus `T` of `H` contains the central torus `Z`, and `p(T) = T/Z` is a maximal
torus of `G`. Over `E` the cocharacter sequence
`0 → X_*(Z) → X_*(T) → X_*(T/Z) → 0` is exact. The map `p` identifies the
simply connected covers of the derived subgroups, so the coroot lattices
correspond. The coroot lattice meets `X_*(Z)` trivially because `Z` meets the
derived subgroup in a finite group. This is a mathematical rationale for the
derived generalization, not a Lean proof.

The statement is about the lattices only. No surjectivity on rational points
of `H → G` follows from it, and none is asserted. Centrality of a normal torus
in a connected group is automatic, but it is kept as a hypothesis, matching
“central torus” and the Library's `IsZExtension`.

## The z-extension case

`IsInducedTorus.isTorus` proves that an induced torus (KP Definition 2.5.1,
`IsInducedTorus`) is a torus: the finite Galois extension in its definition
splits it. `CentralTorusFundamentalExactnessStatement.zExtension` derives,
from the general statement, the three conclusions for every z-extension
`z : ZExtension G` (KP §11.4). It uses the fields of `IsZExtension`: the
induced torus, the closed and central inclusion, the fppf quotient and the
reductivity of both groups. This is the case printed in KP. It is an
implication from the statement, not a proof of it.

The helper `IsInducedTorus.isTorus` is imported from `Langlands.GroupScheme.Torus.Induced`.
