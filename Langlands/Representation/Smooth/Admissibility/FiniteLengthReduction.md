# General finite-length admissibility reduction

Authors: Workers 585, 261 and 863. Worker 863's private general induction in the
published `Langlands.Representation.Smooth.Admissibility.FiniteLengthProof`
provides the restriction-of-scalars intertwiners and induction route. Worker 261
identified the published extension lemma that removes the compact-open cofinality
premise; Worker 585 generalized coefficients and prepared this module.

The public theorem
`Langlands.SmoothRep.isAdmissible_of_finiteLength_of_irreducible` states the
following. Let `k` be any field and `G` a group equipped with any topology. Assume
every irreducible smooth `k`-representation of `G` with carrier in universe `uV`
is admissible. Then every smooth representation with carrier in `uV` and finite
length as a `k[G]`-module is admissible. Admissibility means smoothness and finite
generation of fixed vectors under every open subgroup; over `k` this is finite
dimension. The coefficient, group and representation-carrier universes `uR`,
`uG` and `uV` are independent. No compatibility of the group operations with the
topology, or compact-open cofinality, is assumed.

The irreducible-admissibility hypothesis is explicit. This helper alone does
not prove general reductive rational-points admissibility.

The public definition `Langlands.representationToModuleIntertwiner` constructs
the intertwiner from any representation `ρ` to `Representation.ofModule
ρ.asModule`. The latter uses the restriction of scalars from `k[G]` to `k`.
The map sends `v` first through `ρ.asModuleEquiv.symm` and then through
`(RestrictScalars.addEquiv k k[G] ρ.asModule).symm`. Both maps are bijective,
so their composite is bijective. It is scalar linear and intertwines the
original action with the action recovered from the group-algebra module.
This construction does not require smoothness, finite length or topology.

## Implemented argument

The module imports the published
`Langlands.Representation.Smooth.Admissibility.Extension` and
`Langlands.Representation.Smooth.Transfer.SubquotientProof`, together with the
smooth-category definitions in `Langlands.Representation.Category.Basic`.

The private lemma `module_admissible_of_finiteLength` inducts on Mathlib's
`IsFiniteLength k[G] M`. In the subsingleton case, every fixed-vector space is
subsingleton and hence finite. In the simple-quotient step, the submodule
inclusion and quotient map are converted to intertwiners of the representations
associated with the group-algebra modules. The published
`isSmooth_of_injective` and `isSmooth_of_surjective` give smoothness of the
submodule and quotient. The induction hypothesis gives admissibility of the
submodule. Mathlib's
`Representation.isSimpleModule_iff_irreducible_ofModule` makes the quotient
irreducible, so the theorem's hypothesis gives its admissibility.

The published `isAdmissible_of_extension` then gives admissibility of the middle
representation. Its Noetherian coefficient hypothesis holds for a field. The
required inclusion of the quotient kernel in the inclusion's range follows
from `Submodule.Quotient.mk_eq_zero`. The extension lemma uses finite generation
of fixed vectors and a kernel-image argument for each open subgroup; it needs
neither averaging nor surjectivity on fixed vectors.

Finally, the public bijective intertwiner `representationToModuleIntertwiner` compares a
representation with the one associated to its group-algebra module. Smoothness
transfers along its surjection, and `isAdmissible_of_injective` transfers the
inductively obtained admissibility back to the original representation.

## Provenance and scope

This is internal derived mathematics using the Library and Mathlib lemmas
named above. The source motivation is the finite-length-to-admissible argument
in Renard, *Representations des groupes reductifs p-adiques*, 2026 edition,
VI.6.3, printed page 179 (one-based PDF page 185). That passage reduces to
irreducible admissibility using exact fixed vectors. The implementation uses
the published elementary extension lemma instead. No irreducible-admissibility
theorem from the source is proved or assumed as an axiom here, and no converse
of the finite-length implication is claimed.
