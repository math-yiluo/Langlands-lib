# Uniqueness of the full omega-compatible apartment class

`Langlands.Geometry.Building.OmegaCompatibleApartmentUniquenessStatement.{u}`
is a statement, not a proof. It quantifies over every nonarchimedean local field
`F : Type u`, an affine connected reductive `F`-group `G`, a maximal split torus
`i : S → G` with its monomorphism witness, its actual centralizer datum `C`, and
two apartment data `D` and `E` for `localFieldOrder F`. If both data satisfy the
full axiom V 6 on `C`, then `D = E`.

The data `C : CentralizerDatum i` represent the actual torus centralizer and
include the character-restriction comparison needed to define its valuation.
`D.IsOmegaCompatible C` and `E.IsOmegaCompatible C` mean compatibility on all
centralizer rational points, not just on the split torus. Each `KPApartmentData`
is already a nonempty full equipollence class of V 0–V 5 valuations, normalized
on the split torus and stable under the actual normalizer action. The statement
has no topology-compatibility V 7 or apartment-axiom hypothesis.

## Source and bundled formulation

The source is T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 6.2.6, printed p. 216 (PDF p. 247): any two
omega-compatible valuations of the root datum of `(G,S)` are equipollent.
Definition 6.1.7 defines equipollence using translation by `V(S)`; Definition
6.1.2 separates V 0–V 5, the compatibility condition V 6, and the topology
condition V 7. Thus V 7 is not a premise of Proposition 6.2.6.

The equality of the bundled classes is a derived formulation of that
proposition. Choose a representative from each class. Proposition 6.2.6 makes
the representatives equipollent, and therefore their full translation orbits
are equal. The only data field of `KPApartmentData` is its carrier; the other
fields are propositions. Consequently equality of the two carriers gives
equality of the data. The Library's existing
`KPApartmentData.eq_of_common_mem` in `CrossTorusApartmentComparison` implements
the final equality step once a common valuation is known. Values of the
Library's extended root-function families off the relevant root groups are
forced to be infinity by V 0, so this formulation does not leave extra
unconstrained function values.

The source proof uses Proposition 6.2.5 and Proposition 4.4.3 to compare the
affine spaces equivariantly, then uses the `m(u)` displacement formula of
Proposition 6.2.1 to identify the corresponding valuations. No proof of those
steps or of the proposition is supplied here. In particular this statement
provides neither existence of a class nor a canonical descended building.

The authors' *Corrections and additions*, version of 1 November 2024, pp. 28–29
and 32, were checked: they do not alter Propositions 4.4.3 or 6.2.6. The
correction to Definition 6.1.27 concerns the canonical quasi-split class and is
not used to define either class here.

## Provenance

Derived from the cited source by passing from equipollent representatives to
equality of their full classes. This is a focused prerequisite for comparing
supplied valuation data with source constructions; it does not prove the
normalizer image theorem or add a hypothesis to that theorem.
