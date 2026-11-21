# Heisenberg representations of a simple character (V1)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Proposition (5.1.1), printed p. 158 (PDF p. 170). This is statement V1 of Task 7427.

`HeisenbergRepresentationStatement` quantifies over a nonarchimedean local field `F` and an `F`-vector space `V` in independent universes, an additive character `ψF` with the conductor convention `IsBKAdditiveCharacter` (Task 7422), a simple stratum `S = [𝔄, n, 0, β]` (`S.r = 0`, `S.IsSimple`), a defining-sequence choice `q`, and a simple character `θ ∈ C(𝔄, 0, β)` (`simpleCharacters ψF S.chain S.n S.b q.tail 0`). As in the Library statements of Task 7422, finite-dimensionality of `V` is not a hypothesis; it follows from the existence of a lattice chain. Write `H^1 = simpleHGroup … 1`, `J^1 = simpleJGroup … 1`. The proposition asserts:

- (a) there are `d` and a representation `η` of `J^1` on `Fin d → ℂ` lying over `θ` (`IsHeisenbergRepresentation`, definition 2). Every finite-dimensional representation is isomorphic to one on such a space, so this is existence of a representation lying over `θ`.
- (b) any two representations `η₁`, `η₂` of `J^1` lying over `θ`, on carriers in arbitrary universes, are isomorphic (`Representation.Equiv`). This is the uniqueness in (5.1.1).
- (c) every `η` lying over `θ` (on a carrier `W` in an arbitrary universe) satisfies `η(h) = θ(h) · id` for all `h ∈ H^1`, that is, `η | H^1` is a multiple of `θ`; and `(dim_ℂ W)^2 = (J^1 : H^1)`, where the index is `Subgroup.relIndex H^1 J^1`.
- (d) for such `η`, `I_G(η) = J^1 B_β^× J^1`: the self-intertwining set `representationSelfIntertwining η` (definition 1) equals the pointwise product of the sets `J^1`, `B_β^× = centralizerUnitGroup S.b` and `J^1` in `G = Aut_F(V)`.

BK93 writes the multiplicity and dimension statements for the unique `η(θ)`; the statement asserts them for every `η` lying over `θ`, which is equivalent given (b). Part (d) uses the intertwining direction of definition 1 (`Hom(η^x, η)`); BK93 (5.1.7) uses the opposite direction, which gives the same intertwining set for finite-dimensional smooth representations of compact groups. This is the proposition only; its proof is a separate task.
