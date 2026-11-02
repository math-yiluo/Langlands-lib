# Local flatness and local etaleness

`etaleLocalizedBaseChangeDescent` proves exactly the Library proposition
`EtaleLocalizedBaseChangeDescentStatement`, in five independent universes.
The supporting lemmas develop local algebra for descent of the etale locus.
Flatness of an algebra descends from an algebra over it which is both flat
over the original base and faithfully flat over that algebra. The proof tests
injectivity after tensor product, reflects it by faithful flatness, and uses
the base-change cancellation equivalence to reduce to flatness over the base.

For a local base and a local algebra which is a localization of a finitely
presented algebra, flatness and formal unramifiedness imply formal etaleness.
The residue-field fibre is essentially of finite type and formally unramified,
hence formally etale by Mathlib's field criterion. Mathlib's local smoothness
criterion for flat algebras then gives formal smoothness of the original local
algebra. Combining it with formal unramifiedness gives formal etaleness.

For the differential comparison, `tensorKaehlerEquiv` identifies the
differentials of the pushout `D` over `T` with the extension to `D` of
the differentials of `B` over `A`. Extend this equivalence to `C` and
compose with `tensorKaehlerEquivOfFormallyEtale` for the localization
`D → C`. Tensor base-change cancellation identifies the result with
`C ⊗[B] Ω[B/A]`. Formal unramifiedness over `T` makes the target zero;
faithful flatness over `B` reflects triviality of the differential module.

The wrapper for essential finite presentation unpacks the published
standard-presentation predicate, transports the quotient-algebra
structure through its supplied algebra isomorphism, and applies the
local criterion above. Finally, the exact proposition combines the
flatness descent lemma, the differential descent lemma, and that wrapper.
These are internal helper consequences of the cited-by-name Mathlib results;
no unproved Library statement is used.
