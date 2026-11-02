# Finite length of the smooth dual of an admissible representation

Author: Worker 1149.

`Langlands.SmoothContragredientFiniteLengthStatement.{uG,uV}` states that, for
every topological group `G : Type uG` whose compact open subgroups are cofinal
among its open subgroups, the actual smooth contragredient of every admissible
finite-length smooth complex representation on a carrier in `Type uV` has
finite length. The group and representation universes are independent.
`HasFiniteLength` means finite length of the actual group-algebra module;
`contragredient` is the published space of smooth linear functionals with the
inverse-transpose action.

All hypotheses occur inside the proposition. It makes no assertion that
finite-length representations of an arbitrary topological group are
admissible. It therefore supplies only the generic intermediate target for the
separate closed rational-point and dynamic-Levi targets in
`Langlands.Representation.Aubert.General.PrerequisiteStatements`.

## Derived provenance

This is an internal consequence to be proved from the published smooth-dual
exactness and admissible-duality framework, followed by induction on the
group-algebra module's finite length. The relevant public prerequisites are
`contragredientMap_injective_of_surjective`,
`contragredientMap_exact_of_surjective`,
`contragredientMap_surjective_of_injective_of_compact_cofinal`,
`isAdmissible_iff_of_shortExact`, and
`SmoothRep.isIrreducible_contragredient_iff`.
The last theorem uses the generic irreducibility-transfer lemmas in
`Langlands.Representation.Classification.SupercuspidalContragredientAux`.
The statement does not add an irreducible-admissibility or classification
theorem to these prerequisites.

The source route behind this derived intermediate assertion is Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, I.4.1
(printed page 23), I.5.1 (printed page 26), and III.1.6–7
(printed pages 61–62). Those passages concern exactness, admissible biduality
and simple duals; the finite-length assertion here is their formal algebraic
consequence with the explicitly stated compact-open cofinality hypothesis.
The import supplies the actual constructions and proved duality framework.
This file defines the proposition and does not prove it.
