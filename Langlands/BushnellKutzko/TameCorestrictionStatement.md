# Tame corestriction existence, uniqueness and radical images (T1)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Proposition (1.3.2), printed
p. 28, Definition (1.3.3), its following paragraph, and Proposition (1.3.4),
printed p. 29 (PDF pp. 40–41).

`TameCorestrictionStatement` is a proposition definition, with no proof in this
file; `tameCorestriction` (module `TameCorestrictionProof`) proves it.
For every nonarchimedean local field `F`, finite-dimensional `F`-vector space
`V`, and field `E` acting compatibly on `V`, it asserts:

- there is a `TameCorestriction 𝒪[F] F E V`;
- for any two such maps `s,t`, there is a unit `u` of the published
  `subfieldIntegers F E = 𝔬_E` such that `t(x) = u s(x)` for every `x`;
- for every such `s`, every hereditary order represented by a lattice chain
  `𝓛` and normalized by `Eˣ`, and every integer `n`, the image of
  `𝓛.endFiltration n = 𝔓^n` is the intersection `𝔓^n ∩ End_E(V)`.

The last intersection is written as a preimage under restriction of scalars.
No choice of a chain over `E` and no subfield-order theorem is assumed.
The field action is the representation of a subfield of `End_F(V)` given by
`[Module E V]` and `[IsScalarTower F E V]`; for nonzero `V` the field-action map is injective. The zero space
causes no exception to this statement. All three type universes are independent.

Existence is the consequence of (1.3.4)(i) stated in T1, without additionally
specifying the additive characters used there to construct a map. The unit
comparison is the paragraph following (1.3.3), and the radical image equality is
(1.3.4)(ii). This statement does not include every auxiliary assertion of
(1.3.2).
