# Assembly construction from the published prerequisite propositions

Authors: Worker 864, with Worker 375 contributing the prerequisite and
reciprocity-candidate audit.

This internal construction turns the existing assembly relation into a
chosen full map, assuming `AssemblyWellDefinedStatement`. Its intrinsic
laws show that the map is an assembly and that every other assembly equals
it. The final composition lemma proves `ConditionalAssemblyStatement` from
five explicit prerequisite propositions. The field universe `uF`,
parameter-carrier universe `uP`, and automorphic-carrier universe `uA`
remain independent throughout.

## Construction and uniqueness

Fix a prime `p` and `F : PadicField p`. The supplied
`AssemblyWellDefinedStatement F` says that, for every supercuspidal map
`c0`, positive rank `n`, and class `D : WeilDeligneClass F n`, there exists
exactly one automorphic class related to `D` by
`IsAssembledFrom F c0`.

`assemblyOfWellDefined F hwell c0` uses classical choice to select that
class separately for each `n` and `D`. It therefore has exactly the
published type `FullMap F`; it uses the existing parameter and
automorphic class spaces. The existence part of the chosen unique
witness proves `assemblyOfWellDefined_isAssemblyOf`.

`IsAssemblyOf.eq_of_wellDefined` evaluates two assemblies at each `n` and
`D`. The uniqueness part of `hwell c0 n D` identifies each value with its
unique witness, hence identifies the two values. The published
`fullMap_ext` then gives equality of the full families.
`existsUnique_assembly_of_wellDefined` combines this comparison with the
chosen map and its assembly law. These three laws require no
correspondence predicate on `c0`.

## Composition of inherited properties

`isFullCorrespondence_of_assembly_inheritance` takes the four published
inheritance propositions, a supercuspidal correspondence `c0`, and any
assembly `c` of `c0`.

- `AssemblyBijectiveStatement` applies to the rankwise bijectivity
  component of `IsSupercuspidalCorrespondence F c0` and the assembly
  relation, giving rankwise bijectivity of `c`.
- The supercuspidal correspondence predicate supplies a reciprocity
  candidate `e`, its geometric normalization, and the supercuspidal
  rank-one, determinant, twist, and dual compatibilities. Applying
  `AssemblyOperationStatement` to those components gives the four full
  operation compatibilities.
- `AssemblyLInheritanceStatement` gives `FullPairLCompatibility F c`.
  `AssemblyEpsilonInheritanceStatement`, applied to the same `e` and its
  geometric normalization, gives `FullEpsilonCompatibility F e c`.
  Their conjunction is exactly `FullFactorCompatibility F e c`.

The proof places these results directly into `IsFullCorrespondence F c`,
using the candidate `e` already supplied by `c0`. It needs no separate
reciprocity uniqueness or extension result. Well-definedness is
unnecessary for this particular law because `c` is already supplied
together with its assembly relation.

`conditionalAssembly_of_fivePrerequisites` adds
`AssemblyWellDefinedStatement` to the four inheritance inputs. For each
supercuspidal correspondence it supplies `assemblyOfWellDefined` for the
existence conjunct of the unchanged `ConditionalAssemblyStatement`.
For the universal conjunct it applies the preceding inheritance law
to every supplied assembly.

## Provenance and scope

The provenance is internal. This is classical choice, function
extensionality, and conjunction/existential composition applied to
published definitions in `AssemblyRelation`, `AssemblyTheorems`,
`AssemblyLFactorStatement`, `SupercuspidalSpecification`,
`FullSpecification`, and `FullFactorCompatibility`. No new assertion is
attributed to an external source.

All five prerequisite propositions remain explicit hypotheses. The
module proves none of their representation-theoretic or
Weil–Deligne classification content, and it supplies no theorem of
`ConditionalAssemblyStatement F` without them. This definition candidate
is a helper contribution to the assembly proof task; it does not
complete that task.

The input and output spaces retain arbitrary monodromy and all
irreducible admissible automorphic classes, including nongeneric ones.
No restriction to a special rank, a generic subclass, or a shared
carrier universe is introduced. All quasi-character twists and both
pair-factor clauses are retained through their existing predicates.
