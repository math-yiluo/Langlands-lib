# Finite étale splitting of actual generic-fibre components

`FiniteTypeFiniteEtaleGenericComponentSplitting` states Stacks Project
Lemma 37.24.8 (0551) for actual schemes in any common universe `u`.
For a locally finite-type, quasi-compact morphism `f : X ⟶ Y` with
irreducible target, it asserts the existence of a nonempty open `V`
and a surjective finite étale map `g : Y' ⟶ V.toScheme` from an
irreducible affine scheme. Set `X_V` to the source of the actual open
restriction `f ∣_ V`, and set
`X' = pullback (f ∣_ V) g`. The first pullback projection
`X' ⟶ X_V` is also required to be surjective finite étale.
The second projection `X' ⟶ Y'` has geometrically irreducible
components in its actual generic fibre.

The predicate `FiberComponentsGeometricallyIrreducible f y` makes the
component clause explicit. Its indices are precisely Mathlib's
maximal irreducible subsets of the actual scheme-theoretic
residue-field fibre `f.fiber y`. Each is closed. The predicate
uses the closed subscheme obtained from its vanishing ideal and
composes the actual closed immersion with
`f.fiberToSpecResidueField y`; this morphism to the actual residue-field
spectrum must be geometrically irreducible. The scheme structure
chosen on the closed component is its reduced closed subscheme
structure. It does not assume a supplied family of putative
components or identify components with rational points.

The generic point `η'` of all of `Y'` is part of the existential
conclusion. Schemes are sober, so this is equivalent to the source's
reference to the generic fibre of the irreducible scheme `Y'`.
The source's base-change square is expressed by the actual categorical
pullback of the actual open restriction. This is the usual open base
change `X_V = V ×_Y X`; the further base change is
`Y' ×_V X_V`. The first projection is the source's `g'`,
with target `X_V`. The composite map to `X` is not required to be
finite.

No Noetherianity, quasi-separatedness, separatedness, affineness of
`X` or `Y`, reducedness, properness, smoothness, flatness of `f`, or
restriction on characteristic is assumed. Mathlib's finite-type
convention is `LocallyOfFiniteType` together with `QuasiCompact`.
The irreducible base and the irreducible cover are nonempty. The
generic fibre may be empty, in which case its component predicate
is vacuous, as in the source.

The source is the registered HTML collection
`stacks-generic-geometric-irreducibility-2026-11-04`, file `0551.html`,
Lemma 37.24.8, statement clauses (1)–(7).
The collection SHA256 is
`7779fd83e268ecb0b8a0b8783d039fea6de1ccf33ce652f9bf972c9697b02f8c`;
the file SHA256 is
`90c09df79311d4ad6ea562a3d1813e14cab5b794702822c5e5a81131ab8af6e0`.
The retained proof contains the corrected nilradical wording.

This file supplies proposition definitions only. It does not prove
the existence of the finite étale cover or spread geometric
irreducibility away from the generic fibre. The latter is the
separate Stacks 0559 target. Together these are substantial inputs to
Stacks Lemma 37.28.4 (055G), used for the geometric-connectedness
part of Conrad's Theorem 3.4(2).
