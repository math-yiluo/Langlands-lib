# Rank-one witnessed realization and relative isometry operation reduction

This internal module defines the proposition
`Langlands.Global.PoleComparison.RelativeWitnessedCharacterRealization`
and proves the algebraic reduction of the relative isometry operation target to
actual witnessed generator constructions. It retains the independent field,
Weil-carrier and presentation-factor universes throughout. The reduction is not
a proof of the unconditional
`Langlands.Global.PoleComparison.RelativeIsometryOperationStatement`.

For a specified local reciprocity candidate `e` and continuous local character
`χ`, `RelativeWitnessedCharacterRealization F E c v e χ` means that an actual
`WitnessedGenerator F E c v` has Weil and automorphic lattice inclusions equal
to the two corresponding rank-one basis generators. The Weil character is the
pullback through `e`; the automorphic class is the rank-one class of `χ` itself.
The two equalities take place in the full lattices after including the unitary
lattices. Forming this proposition assumes neither geometric reciprocity nor
modulus one and asserts no witness by itself. Its deduction from twist closure
requires the stated modulus-one proof and an actual local-map family.

`localMapFamilyOfClassField` constructs a characterized local-map family from
proofs of the published local reciprocity existence and uniqueness statement
and local relative Weil map existence statement, together with the arithmetic
class-family certificate. It chooses a local reciprocity candidate and a
characterized local map at every pair of finite places. Neither existence
statement is asserted here. `relativeIsometryOperations_of_classField`
composes this construction with the algebraic reduction.

The imported dual and twist closure predicates concern complete actual
witnessed generators at the original parameters. Their conditional
constructions and all global prerequisites remain separate inputs; importing
them supplies no proof of those prerequisites. The bundled supporting pairs
are unchanged constructions by Workers 69 and 163. Both workers contributed
the generator interfaces used by the assembly.

The implemented algebraic reduction uses only the first, generator-fixing
conjunct of `RelativeGeneratedPositiveIsometry`. The linear graph map
`x ↦ (x,T x)` has a submodule as its range, containing every witnessed pair.
Hence it contains the entire paired span (`relative_pair_on_graph`).
The published `exists_pair_of_mem_weilImage` then shows that each `(x,T x)`
belongs to that paired span (`relative_graph_mem_pair`).

For a pair of linear operations `A,B`, actual compatible witnessed generators
imply that the paired span is contained in its preimage under `A.prodMap B`.
Applying this to `(x,T x)` gives the exact source-membership witness and
commutation identity (`relative_operation_of_witnessed`). This argument
includes signed integral combinations and needs neither a basis nor ambient
spanning. The conditional assembly specializes it to the published dual and
unitary twist equivalences. For rank one it applies the generator-fixing
identity directly to the supplied generator.

The character premise is now derived from the concrete trivial witnessed
generator in `RelativeTrivialGenerator`. Twisting a rank-one trivial Weil class
by the pullback of `χ` yields exactly the rank-one class of that pullback. This
uses `IsRankOneWeilCharacter.twist` and uniqueness of the character class.
The automorphic counterpart uses `IsRankOneCharacter.characterTwist` and the
proved graph description of `supercuspidalTwist`. Inclusion of both unitary
lattices commutes with twisting. Applying witnessed twist closure to the actual
trivial generator thus gives a witnessed generator for every required character,
as `relativeWitnessedCharacterRealization_of_twist` proves.

This reduction is internal linear algebra derived from the published
`RelativeImages` and `RelativeIsometryOperationStatement` definitions.
The public theorems used are
`RelativeGlobal.witnessed_pair_mem`, `RelativeGlobal.witnessed_weil_mem`,
`RelativeGlobal.witnessed_automorphic_mem`, and
`RelativeGlobal.exists_pair_of_mem_weilImage`, together with Mathlib's
`Submodule.span_le`, `LinearMap.range` and linear map operations.
The additional character reduction uses
`RelativeGlobal.trivialWitnessedGenerator_weil_include`,
`RelativeGlobal.trivialWitnessedGenerator_automorphic_include`,
`Correspondence.IsRankOneWeilCharacter.twist`,
`Correspondence.IsRankOneWeilCharacter.class_unique`,
`Correspondence.IsRankOneCharacter.characterTwist`, and
`Correspondence.isSupercuspidalCharacterTwist_iff_eq_supercuspidalTwist`,
as well as the two unitary-twist inclusion identities.
No source literature is used to justify an unproved construction. The
certified pole comparison hypothesis is not needed for this conditional
algebraic reduction. The final proof must still retain every quantifier and
hypothesis of the published target, leave that pair and its imports unchanged,
and avoid downstream local Langlands and globalization results.

`relativeIsometryOperations_of_globalInputs` discharges both closure
predicates using the concrete conditional constructions. On the dual side,
`relativeWitnessedDualClosure_of_centralComparison` uses the given central
comparison to obtain each generator's unitary central character, then invokes
the actual cuspidal contragredient, presentation, local compatibility and
presented association inputs. On the twist side,
`relativeWitnessedTwistClosure_of_globalInputs` applies the complete existential
twist constructor to every original generator, using the arithmetic
class-family certificate, determinant-multiple existence, presented
association, local transfer reciprocity and unitary extension at the specified
field and finite place. The class-field existence inputs construct the local
map family needed by the trivial generator.

The final conditional theorem,
`relativeIsometryOperationStatement_of_globalInputs`, quantifies over the
target's original fields, arithmetic class family, finite place, additive
character, certified pole comparisons and generated positive isometry. It
specializes the preceding theorem. Its eleven remaining proof parameters are
local geometric reciprocity existence and uniqueness, local relative Weil map
existence, associated central-character comparison, the four actual
contragredient statements, the two actual determinant-twist statements, local
transfer reciprocity, and arbitrary unitary local-to-Hecke extension. The last
parameter is written out in the exact natural-completion topology of
`UnitaryLocalCharacterExtensionStatement`; no compact-quotient instance or
finite-order restriction is added to it. This theorem has the exact target
only after all eleven arguments have been supplied. Its conditional
type is an intermediate deduction; it does not meet the exact final proof
obligation.
