# Number-field isomorphisms on adeles and idele classes

This module transports the actual Mathlib adeles, ideles and idele classes
along an isomorphism `e : K ≃+* L` of number fields in independent universes.
It imports the infinite-place and finite-place construction groups.
No arithmetic maps or their compatibility laws are assumed as input.

`adeleEquiv e` combines the infinite and finite adele ring isomorphisms
using Mathlib's product definition `NumberField.AdeleRing (𝓞 K) K`.
Both directions are continuous. `adeleHomeomorph` and
`adeleContinuousMulEquiv` bundle that same map. The diagonal formula,
identity and composition follow factorwise from the component laws.
The `_infinite_apply` and `_finite_apply` theorems expose the exact completed
coordinate formulas, including the necessary place pullback.

`ideleEquiv e` uses `Units.mapContinuousMulEquiv`. Thus the topology tracks
both the value and inverse of an idele, as Weil requires, and is not the
topology induced only by the value map into adeles. Its diagonal formula
uses the actual map of field units. This proves `ideleEquiv_principal`:
the image of the source principal subgroup is precisely the target principal
subgroup.

`ideleClassEquiv e` is therefore `QuotientGroup.congr` on the actual
principal-idele quotients. Continuity in both directions follows from the
quotient topology's universal property and the corresponding idele continuity.
The construction does not replace the quotient carrier or assume the quotient
map is injective. `ideleClassEquiv_mk` is its formula on representatives.
Identity and composition are proved by quotient induction and the idele laws.

Local insertion maps have value one outside the chosen place. The
`adeleEquiv_ofCompletion` and `adeleEquiv_ofAdicCompletion` proofs compare
coordinates, splitting whether the coordinate is the distinguished place.
Reindexing is injective and all completion maps preserve one. Passing to units
and then to the quotient proves the matching `ideleEquiv_*` and
`ideleClassEquiv_*` local insertion formulas.

`adeleAut`, `ideleAut` and `ideleClassAut` are monoid homomorphisms from the
actual automorphism group `K ≃ₐ[ℚ] K` to the respective automorphism groups.
Composition order agrees with the multiplication of field automorphisms.
`ideleClassAction` supplies the corresponding installable multiplicative
action, and every acting map is continuous.

For a CM field, `ideleClassComplexConj` specializes the construction to
Mathlib's actual field involution `IsCMField.complexConj K`.
It is continuous, its square is the identity, and its formula on representative
ideles is explicit. On an idele representative's infinite coordinates,
`ideleComplexConj_infinite_coordinate` identifies the action with ordinary
complex conjugation under the completed complex embedding. A local coordinate
is not asserted to be well-defined on an idele class. A character can compose
directly with `ideleClassComplexConj.toMonoidHom`; no character existence
or self-duality assertion is part of the construction.

Sources: Weil, *Basic Number Theory*, second edition (1973), Chapter IV
section 1, Definition 1 and diagonal embedding, printed pp. 59-60/PDF pp. 76-77;
section 3, Definition 2 and Proposition 2, printed pp. 71-72/PDF pp. 88-89;
section 4, Theorem 6 and the quotient by field units, printed p. 76/
PDF p. 93. Registered `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
Henniart (2000), sections 3.3-3.6, printed pp. 449-451/PDF pp. 11-13,
motivates the concrete CM action; registered `henniart-2000-simple-proof`,
SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Tate, *Number theoretic background* (1979), sections 1.5-1.6, printed
pp. 7-9/PDF pp. 16-18 of Corvallis Part II, supplies the arithmetic action
and local insertion context. Registered
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The sources are used for the arithmetic objects and conventions, not as
assumptions of reciprocity.

No norm or reciprocity map is assumed or constructed by this module.
Finite-extension norms remain required work under the assigned task.
The imported project construction groups must be independently accepted and
published before this pair can be submitted as a dependent contribution.
