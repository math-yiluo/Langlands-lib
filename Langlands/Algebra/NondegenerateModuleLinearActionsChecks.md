# Interface and degenerate-case checks for simultaneous linear actions

Authors: Worker 1187 and Worker 6. The original-structure constructor probes,
explicit named-ring probes and general zero/empty-family checks adapt the
comparison draft supplied by Worker 6. Worker 1187 wrote the complete generic
and explicit unequal-universe interfaces, adapted those probes to the present
constructors and added the concrete zero-ring/carrier construction. This
module is an internal verification companion to
`Langlands.Algebra.NondegenerateModuleLinearActions`; its mathematical
provenance and source boundaries are those explained in that module's paired
Markdown. It asserts no additional numbered result from Renard.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, content SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Relevant passages are conventions and I.1.1–I.1.3, printed pp.5–9 / PDF11–15;
I.1.8, printed pp.13–14 / PDF19–20; and I.2.1, printed p.14 / PDF20. The
commutative-semiring and arbitrary-indexed-family constructions checked here
are internal generalizations of those complex action constructions.

## Complete declaration types

Each generic example assigns a declaration as a whole with `@` and explicit
universe parameters. It does not establish only an already applied equality.
The individual checks cover `endRing`, `endModule`, intrinsic `act_smul`,
`linearEnd`, `completedHom` and `completedHom_comp_canonical`. Family checks
cover the named product ring/module, `original`, `completed`, both coordinate
projections, the entire canonical composite and entire projection identities.
The expected types explicitly install canonical scalar modules and named rings
and modules wherever their operations enter the homomorphism types.

The coefficient, algebra, index and carrier universes are arbitrary and
independent. Additional whole-type assignments for the key maps, projections
and canonical compatibility use `(uK,uA,uI,uM) = (0,1,2,3)` and `(3,2,1,0)`;
the individual completed-map assignments use the corresponding three
universes. This tests unequal universes in both directions.

## Structure selection under competition

`CompetingOriginalStructures` and `CompetingOriginalIndividual` place other
original algebra rings, carrier groups and algebra actions in instance scope.
The whole constructor assignments explicitly select the specified original
ring, algebra scalars, bilinearity, additive groups and actions. Their
nondegeneracy proofs and outputs remain unapplied in the checked declarations.
The expected types reinstall the selected originals, so all hypotheses and
actual original action types refer to those same structures.

`CompetingConstructedStructures` supplies competing carrier scalar modules,
endomorphism rings/modules, a product ring/module and a completed ring.
Expected whole types explicitly use `NondegenerateScalars.module`, `endRing`,
`endModule`, `productRing`, `productModule` and
`IdempotentedRingRightLimit.ring hA`. Definitional equalities identify
`endRing` with the actual `Module.End.instRing` on canonical scalars and
`productRing` with the actual `Pi.ring` on those named coordinate rings.
Further examples check whole original/completed maps, both whole projections
and whole canonical/projection composites for those precise structures.
The complex examples check complete types of the exact complex aliases on the
original carriers, using `NondegenerateScalars.complexModule`.

## Zero rings, zero modules and empty families

The general zero-ring check assumes `Subsingleton A`. For a fixing idempotent
it uses `linearEnd_apply_eq`, identifies the family coordinate with zero and
uses the original `NonUnitalModule.zero_smul`. Additive-map extensionality
then identifies the entire completed additive-endomorphism function with zero.
The zero-carrier check assumes `Subsingleton M`, installs canonical scalars
and proves the entire linear-endomorphism function is zero by extensionality.
The analogous family check identifies the entire completed map's underlying
function with zero when all carriers are subsingletons.

For an empty indexing type, the actual dependent product is a subsingleton.
Homomorphism extensionality and elimination of a nonexistent index prove that
`original` equals every nonunital algebra homomorphism of its stated type,
and `completed` equals every ring homomorphism of its stated type. In
particular their unital target ring is permitted to be the zero ring.

Finally the concrete zero-object example uses the actual one-element ring
`PUnit` and one-element carriers indexed by `Unit`. The original additive
algebra action is explicitly `NonUnitalModule.ofEndHom 0`. Idempotentedness
comes from the original ring, and each original carrier is nondegenerate
using the zero idempotent. The example supplies actual inhabitants of both
whole homomorphism types using `original` and `completed`. No prior scalar
module on a carrier is supplied to either constructor.

All examples are complete Lean terms or kernel-checked proofs. These checks
verify the stated interfaces and degenerate cases; they do not establish
independent acceptance or publication, or any separation, injectivity,
classification or categorical-centre assertion.
