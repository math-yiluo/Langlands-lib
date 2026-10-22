# Arithmetic transport at infinite places

This construction uses Mathlib's actual infinite places, their completions, and
`NumberField.InfiniteAdeleRing`. A field homomorphism pulls back a place. The same
homomorphism is an isometry after equipping each field with the corresponding
absolute value, so its extension to the uniform completions is continuous.
Coordinatewise extension and place pullback define `infiniteAdeleMap`.
The construction carries the diagonal element of the source field to the
diagonal image of its field homomorphism.

For an isomorphism `e : K ≃+* L`, `infinitePlaceEquiv e` goes from the
places of `L` to those of `K`: the source coordinate for a place `p` is
`p.comap e.toRingHom`. `infiniteCompletionEquiv e p` is the ring
isomorphism between these completed fields. Its underlying map is
`infiniteCompletionMap e.toRingHom p`, and the same function is bundled
as an isometry equivalence and a homeomorphism. These constructions extend
the actual field map on the dense field subspace. No completion isomorphism
is assumed as input.

For number fields, identity and composition follow from this diagonal formula,
continuity, and Mathlib's weak approximation theorem: the diagonal number field
is dense in its infinite adele ring. Applying the maps for a field isomorphism
and its inverse gives `infiniteAdeleEquiv`. Both directions are continuous;
`infiniteAdeleHomeomorph` bundles the same underlying equivalence as a
homeomorphism. The source and target number fields have independent universes.

`infiniteAdeleAut` is a monoid homomorphism from the actual group
`K ≃ₐ[ℚ] K` to ring automorphisms of the infinite adele ring. Thus its
identity and multiplication laws are proved, and every resulting automorphism
is continuous. For a CM number field, `infiniteComplexConj` applies this
arithmetic transport to Mathlib's `IsCMField.complexConj K`. It is a
continuous involution and agrees with field conjugation on diagonal elements.
Conjugation fixes the infinite places. Under the chosen complex embedding
of each completed field, `infiniteComplexConj_coordinate` identifies its
action with ordinary complex conjugation. The proof first checks this
identity on the diagonal using Mathlib's CM embedding theorem, then uses
density and continuity. This gives a concrete arithmetic action, without
assuming any character or self-duality condition.

The field-homomorphism and completed-field constructions only require fields;
the identity/composition proof on infinite adeles uses `NumberField K`.
The equivalence uses number-field instances for both fields, and the CM part
additionally uses `IsCMField K`. There is no universe resizing.
The formal dependencies are pinned Mathlib's `InfinitePlace.comap`,
`WithAbs.map`, completion ring maps and isometries, weak approximation
(`InfiniteAdeleRing.denseRange_algebraMap`), and its CM conjugation lemmas.
This module imports no other project construction.

The definitions are derived from Andre Weil, *Basic Number Theory*, second
edition (1973), Chapter III section 1, Definitions 2-4, printed pages 43-45
(PDF pages 60-62), and Chapter IV section 1, Definition 1 and the diagonal
embedding, printed pages 59-60 (PDF pages 76-77).
Registered source `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
Transport along an isomorphism is the direct application of these definitions.
Weil's complex local module is the square of the usual absolute value; Mathlib
uses the unsquared complex absolute value for its completion metric. These
determine the same completion topology.

The CM specialization is the infinite-place part of the arithmetic conjugation
used by Guy Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique* (2000), sections 3.3-3.6, printed pages
449-451 (PDF pages 11-13). Registered source
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Those passages motivate the later idele-class character action; this module
does not claim to construct Henniart's characters.

This first construction group concerns infinite places only. It does not yet
construct finite adele transport, an action on full idele classes, or a norm for
a finite extension. Those remain required parts of the assigned task.
