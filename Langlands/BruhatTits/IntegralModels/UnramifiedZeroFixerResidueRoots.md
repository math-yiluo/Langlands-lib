# Actual residue tori and root groups of unramified zero-fixer models

This internal supporting construction identifies the actual residue fibres of the
integral torus and root models in `IntegralSplitTorusData`. All rings, fields and
schemes have arbitrary universe `u`. The full special fibre is used throughout.

`specialFibreTorus` is the pullback of the integral split torus along the actual residue
quotient map, and `specialFibreInclusion` is the pullback of its integral inclusion.
The torus stays split, and a closed integral inclusion stays closed. The character
and cocharacter specialization equivalences use the generic torus identification
and the published split-lattice base-change equivalences. Both pass through the
same integral torus, so `latticePairing_specialization` preserves the integer
character/cocharacter pairing by `latticePairing_congr` and
`latticePairing_baseChange`.

For a smooth ambient model and any nonzero generic character,
`rootModelMap_specialFibre_isRepresentedBy` proves that the constructed root
model's actual special-fibre map represents the root subgroup of the specialized
character. This is equality of subgroup functors on every scheme test, with a
monomorphic representing map. The proof base changes the integral representability
from `IntegralModel.SplitRoot.integral_properties` and applies
`RelativeRoot.subgroup_baseChange`. The representing map is also a closed
inclusion, by base change of the constructed integral closed inclusion. No
nontriviality or root-support equality is asserted for arbitrary characters.

Over a Henselian local domain with algebraically closed residue field, if the
ambient generic group is connected reductive, the generic inclusion is a maximal
split torus and the integral inclusion is closed,
`specialInclusion_isMaximalTorus` proves maximality in the full special fibre.
It transports generic maximality through the specified torus isomorphism using
the published `IsMaximalSplitTorus.iso_comp`, then applies
`IntegralModel.isMaximalTorus_specialFibre_of_generic`. The smooth full special
fibre may be nonreductive.

The final two lemmas apply these constructions to
`unramifiedZeroFixerIntegralSplitTorusData`. They supply residue maximality and
actual residue-root representability for every supplied smooth zero-fixer model,
every apartment subset and every zero datum. Henselianity and the algebraically
closed residue field are the published properties of `fixedFieldIntegers F`.
No model with the full one-fixer as integral points is assumed.

This unit derives from the named Library constructions and proves no new
literature translation. It supplies the actual residue-root interpretation needed
when an incident facet image contains a constructed root-model image. Determining
the entire incident image, excluding the other root directions, classifying all
parabolics, and proving the host facet-order bijection remain further obligations.

The residue torus, its inclusion, character specialization and root-model
representability and closedness are reused from
[IntegralRootSpecialFibre](IntegralRootSpecialFibre.md). This module adds
cocharacter specialization, pairing preservation, maximality and their
zero-fixer applications on those same constructions.
