# Unique factorization through the smooth part: implemented proof

`Langlands.smoothPartUniversalProperty` proves the complete adjacent
proposition `SmoothPartUniversalProperty`, accepted statement artifact
`16500d55-deee-48eb-b34b-91e7fe62065f`, version 1. Worker 0 authored the
proof and initial explanation in task draft revision 1, content key
`19cceb5ca179fd177c1bd32d68c31b4db407bcc460d1e46b92266039956a299f`.
Worker 30 checked the exact target, dependencies and proof, and expanded
this explanation. Worker 0 is retained as coauthor.

The witness is the constructed `smoothLift hSigma f`. The equation
`smoothInclusion_comp_smoothLift` holds by extensionality because both maps have
the same underlying function. For uniqueness, the equality of composites is
evaluated at each vector. Subtype extensionality then identifies the values of
any proposed lift with the canonical lift; linear-map and intertwiner
extensionality identify the bundled maps.

More precisely, `smoothLift_unique` assumes
`(smoothInclusion rho).comp lift = f`. Evaluating this equality at `v`
gives `(lift v).val = f v`. The value of `smoothLift hSigma f` has
underlying value `f v` by its accepted codomain-restriction definition.
`Subtype.ext`, `LinearMap.ext`, and `Representation.IntertwiningMap.ext`
therefore prove equality of the bundled intertwiners, including their
linear and equivariant structure. The factorization lemma proves the
displayed composite equation, in that order, by `ext v; rfl`.

The existence construction already proves its codomain-membership obligation:
a fixing open subgroup for a source vector fixes its image under `f` by
equivariance. The present proof uses that accepted construction directly;
it does not assume a separate universal property.

The closing proof explicitly introduces the target's topological-group
instance, representations, source smoothness, and intertwiner. It packages the
canonical witness, its factorization equation, and the uniqueness lemma.
No theorem from the separate basic-property or smoothness-transfer proof modules
is imported.

The helpers require `IsTopologicalGroup G` to form the smooth-part action.
The closing theorem uses `omit [IsTopologicalGroup G]` and then introduces
the instance at the proposition's internal binder. Thus its ambient
parameters are exactly a commutative ring, a group with a topology, and
the two module structures. `R`, `G`, `V`, and `W` have independent
universes. Smoothness is required only for the quantified source `sigma`;
the target `rho` is arbitrary. There is no assumption of admissibility,
finite generation, local compactness, or topology on the modules.

The construction is internally derived from Casselman's smooth-vector subspace:
`casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, Section 1, page 2, first two paragraphs.
See [the target](UniversalStatement.md) and [definitions](Definitions.md) for
the original file and exact hypotheses.

Worker 30 read the original June 16, 2019 PDF pages 1-2 and verified the
fingerprint above. Page 2 supplies the open-fixing-subgroup definition
and stability of smooth vectors under the group action. Unique
factorization is an internal consequence of these constructions, rather
than a separately numbered theorem in that passage. The chapter's
stronger locally profinite, countability, and Noetherian rational-coefficient
assumptions are not used in this proof.

The target is independently published at
`a28679cf25a4ce001af4e724a51fd7db72864cd3`, with receipt
`ed612220-3b7d-4722-aac7-8b1e058f92fd`. Fresh fetch confirms current availability
at `bb596ce619f2174816281f508cce65b3303beeb4`, with no changed files or
unavailable dependencies. Its target fingerprint is
`45f835d980b6814c9f6ae0fdcc0e7d13f0261fabbb3c7144dc0fd2d5795b6bb6`.
The only imported project target is this statement. Its exact transitive
definitions are smooth-part construction
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` and foundation
`665022df-625b-44ae-9dbd-425f6e266bab`, both version 1.
Worker 30 matched all six local dependency files to their effective
accepted pairs. Their publication references are:

| Dependency | Publication commit | Independent receipt |
| --- | --- | --- |
| Smooth-part construction | `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919` | `1f969dc8-79b0-4e70-adf8-502752d70c6a` |
| Smoothness foundation | `10c81beaaff024987cf2945c64d0c9511f6cb686` | `a26076cd-7da3-4621-992f-5c0207f7fe1e` |

These recorded publications establish the dependencies' current accepted
status; their preserved Markdown still contains historical draft labels.
The proof imports only `UniversalStatement`. The pinned Mathlib
`RepresentationTheory/Intertwining.lean`, lines 51-55 and 213-223,
supplies intertwiner extensionality and the composition convention used here.

Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The whole-target theorem retains four independent universes and introduces the
topological-group instance only at the target's internal binder. The two helper
lemmas and closing theorem belong to this one proof contribution.
Native compilation and assignment to the entire accepted proposition with
four independent universes passed with exit code 0. The check has no
external topological-group instance. The inspected axiom closures of both
helpers and the closing theorem contain only `propext`, `Classical.choice`,
and `Quot.sound`. These are development checks. Registered independent proof checking,
independent semantic review and current Library publication are required
for acceptance. No placeholders or project axioms are introduced.
