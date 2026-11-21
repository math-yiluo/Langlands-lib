# Complex conjugation commutes with the smooth contragredient

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, IV.2.1, opening paragraph, printed p. 96 (PDF p. 102).
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`Langlands.Renard.CompactRepresentation.ConjugateContragredientStatement`
expresses Renard's identification of the Hermitian contragredient with
the smooth contragredient of the complex-conjugate representation.
`ConjSpace V` gives the conjugated scalar multiplication, and
`ConjSpace.rep` acts by the original operators on the underlying additive
group. The two constructions use `smoothContragredient` on the actual actions.

For a smooth complex representation on a Hausdorff locally compact totally
disconnected group, the statement asserts a linear \(G\)-equivariant
equivalence
\[
\overline{\widetilde{\rho}}\ \simeq\ \widetilde{\overline{\rho}}
\]
with the evaluation formula \(\overline{\ell}(\overline{x})=
\overline{\ell(x)}\). This formula specifies the comparison between the
two carriers. The group and the representation carrier have independent
universes.
