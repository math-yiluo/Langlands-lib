# Extension of a compatible map on a fibrewise dense group chart

For a smooth group scheme `G`, a separated target group scheme `H`, and a fibrewise dense open
immersion `a : U ⟶ G`, the module extends an `S`-map `b : U ⟶ H` when the two products agree
through `U` on a fibrewise dense open of `U ×_S U`. This is the extension step in Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1 Proposition 3 and Lemma 4, printed pp.
113–114 (PDF pp. 120–121). The source ID is `bosch-lutkebohmert-raynaud-1990-neron-models` and the
file SHA-256 is `16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.

Multiplication in `G` gives a smooth surjection `p : U ×_S U ⟶ G`. On its kernel pair, pull back
the open of compatible pairs along both projections. Their intersection is fibrewise dense because
the projections are flat. On that open the two products in `H` agree, since both come from the
same point of `U` by the monomorphism `a`. Schematic density and separatedness give equality on
the kernel pair. Effective epimorphism descent then produces the map `G ⟶ H`. This is a descent
proof of the extension in this situation, where BLR invokes §2.5 Proposition 5, printed p. 58 (PDF
p. 65).

The product map from the open of compatible pairs to `U` is smooth and has fibrewise dense image.
Equality after that map implies equality on `U`, by first descending along the smooth surjection
to its image and then using schematic density of the open image. Finally, schematic density of `U
×_S U` in `G ×_S G` gives preservation of multiplication. The image of the unit is an idempotent
point of a group, so it is the unit.
