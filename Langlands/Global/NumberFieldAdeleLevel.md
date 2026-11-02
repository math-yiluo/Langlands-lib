# Actual full adelic levels of a number field

Author: Worker 208.

For an actual number field `K`, `NumberFieldPlace K` is the disjoint union
of the existing archimedean places and height-one primes of its ring of
integers. For a finite set `S` of finite places, `numberFieldLevelPlaces`
adds all archimedean places. The membership lemmas identify each part, and
`numberFieldLevelPlaces_nonempty` uses the existence of an archimedean
place. Thus this indexing satisfies Conrad's requirement that the
all-place set be nonempty and contain every archimedean place, even when
the finite part `S` is empty.

`numberFieldAdeleLevel K S` is the subring of the already existing
`Adeles K` whose finite coordinates are integral away from `S`. Its
archimedean coordinates are unrestricted. This is an actual subring of
Mathlib's full number-field adele ring, rather than another adelic carrier.
It is open because projection to the finite adele ring is continuous and
the existing finite level is open. The monotonicity lemma and
`numberFieldAdeleLevelMap` give the literal inclusions for `S ⊆ T`; the
coercion lemma identifies them with the identity on underlying full adeles.

`numberFieldAdeleLevelDiagonal` restricts the actual diagonal homomorphism
from `K` to the existing ring of `S`-integers and corestricts to the full
level. Its finite integrality follows from the existing finite-level
diagonal map. The declared algebra structure comes from this map.
The finite and infinite coordinate lemmas identify both parts of this
action with the actual completion maps from `K`.

`numberFieldAdeleLevelSplit` is the explicit ring equivalence between the
full level and the product of its archimedean part and actual finite level.
`numberFieldAdeleLevelProductEquiv` composes it with the already constructed
finite local-factor ring equivalence. Its three coordinate formulas give
the actual archimedean completion, finite completion and completed-integer
coordinates. These are ring equivalences; this construction unit does not
assert the product homeomorphism or a colimit universal property.

This is derived arithmetic infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.1,
the definition and conventions for `A_{F,S}`, and printed pp.6–8,
Theorem 3.6 and the local factors in (3.6.1). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The Lean implementation combines the existing number-field adele ring and
its projections with the Dedekind finite-level construction. Its intrinsic
lemmas explain that combination and its canonical coordinates.

This file covers the number-field level rings. The general global
function-field construction, realization of omitted places, independence
of a chosen function-field presentation, model descent, scheme-point
comparisons and their nonaffine topologies remain separate obligations of
the whole-paper program.
