# `β`-extensions

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Definition (5.2.1), printed p. 166 (PDF p. 178). This is definition 3 of Task 7427.

## Setting

As in `HeisenbergRepresentation`: `G = Aut_F(V)`, `L` the `𝔬_F`-lattice chain of `𝔄`, and `J^m(β, 𝔄) = simpleJGroup L n β tail m`, `J(β, 𝔄) = simpleJ L n β tail = J^0(β, 𝔄)` (Task 7422, definition 2). `B_β^×` is `centralizerUnitGroup β`, the units of `A = End_F(V)` commuting with `β`; when `F[β]` is a field this is `Aut_{F[β]}(V)`. `U(𝔅_β) = relativeUnitFiltration L β 0 = B_β^× ∩ U(𝔄)` (Task 7422).

## Definitions and lemmas

- `relativeUnitFiltration_le_simpleJ`: `U(𝔅_β) ≤ J(β, 𝔄)`. An element `g ∈ U(𝔅_β)` lies in `U(𝔄)`, and `g` lies in the summand `𝔄 ∩ B_β` (`centralizerLattice L β 0`) of the lattice `𝔍(β, 𝔄)`, so `g` is one of the generators of `J(β, 𝔄)`.
- `simpleJGroup_one_le_simpleJ`: `J^1(β, 𝔄) ≤ J(β, 𝔄)`.
- `IsBetaExtension L n β tail η κ`, for a representation `η` of `J^1(β, 𝔄)` and a representation `κ : Representation ℂ J(β, 𝔄) W'`: `W'` is finite-dimensional, `κ` is smooth (`IsSmoothRepresentation`), the restriction of `κ` to `J^1(β, 𝔄)` is isomorphic to `η` (a `Representation.Equiv`), and every `y ∈ B_β^×` lies in `representationSelfIntertwining κ`, that is, `y` intertwines `κ` in the sense of `RepresentationIntertwining` (definition 1).

BK93 defines `β`-extensions of the representation `η` lying over `θ ∈ C(𝔄, 0, β)`. The predicate takes `η` as an argument and does not itself require that `η` lies over a simple character; the definitions and statements that use it (simple types, statements V2 and V3 of Task 7427) supply `IsHeisenbergRepresentation … θ η` with `θ ∈ C(𝔄, 0, β)` as a separate condition. Condition (i) of (5.2.1), `κ | J^1 = η`, is read as an isomorphism of representations of `J^1(β, 𝔄)`, which allows `κ` and `η` to have different carrier spaces.

Existence of `β`-extensions and their classification up to twisting, BK93 (5.2.2)(i)–(ii), are statement V2 of Task 7427, not part of this definition.
