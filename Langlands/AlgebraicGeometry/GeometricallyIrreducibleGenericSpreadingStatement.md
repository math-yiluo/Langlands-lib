# Geometric irreducibility near an actual generic fibre

`FiniteTypeGeometricallyIrreducibleGenericSpreading` states Stacks Project
Lemma 37.27.5 (0559) for arbitrary schemes in a common universe `u`.
For an actual scheme morphism `f : X ⟶ Y` that is locally of finite type and
quasi-compact, and a point `η` generic for all of `Y`, geometric
irreducibility of the actual residue-field fibre implies that there is an
open `V` containing `η` for which the actual restricted morphism
`f ∣_ V` is geometrically irreducible.

The generic-point hypothesis means that the closure of `{η}` is all of
`Y`; it includes irreducibility and nonemptiness of `Y`. Finite type is
written using Mathlib's two classes `LocallyOfFiniteType` and
`QuasiCompact`. No quasi-separatedness, separatedness, affineness,
Noetherianity, properness, smoothness or flatness hypothesis is imposed.
The generic fibre is Mathlib's scheme-theoretic pullback along
`Y.fromSpecResidueField η`, with structure morphism
`f.fiberToSpecResidueField η`. It is not a set of rational points.

Mathlib's `GeometricallyIrreducible` requires every pullback along a map
from a field spectrum to have an irreducible, nonempty underlying space.
By its fibre criterion, the conclusion says that every actual
residue-field fibre of the restriction is geometrically irreducible.
This is exactly the source's conclusion about fibres over the nonempty
open subscheme. Every nonempty open of a space with generic point `η`
contains `η`, so explicitly retaining `η ∈ V` does not strengthen the
source assertion.

The source is the registered HTML collection
`stacks-generic-geometric-irreducibility-2026-11-04`, file `0559.html`,
Lemma 37.27.5, statement. The collection SHA256 is
`7779fd83e268ecb0b8a0b8783d039fea6de1ccf33ce652f9bf972c9697b02f8c`;
the individual file SHA256 is
`6dc5e34232f56f8111e2581afd2822d79276b962e4110f23eb411ab8b166ca1f`.
The retained version uses the corrected hypothesis about the *generic*
fibre.

This file supplies a proposition target only. Its proof, the finite
generic splitting of components used with it, and the resulting generic
constancy of geometric connectedness are separate obligations. In the
Conrad program, this is the spreading input used in Stacks Lemma 37.28.4
(055G), supporting the geometric-connectedness part of Conrad's
Theorem 3.4(2).
