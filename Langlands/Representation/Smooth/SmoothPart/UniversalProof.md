# Unique factorization through the smooth part: implemented proof

`Langlands.smoothPartUniversalProperty` proves the complete adjacent
proposition `SmoothPartUniversalProperty`. The exact target, dependencies and
proof were checked.

The witness is the constructed `smoothLift hSigma f`. The equation
`smoothInclusion_comp_smoothLift` holds by extensionality because both maps have
the same underlying function. For uniqueness, the equality of composites is
evaluated at each vector. Subtype extensionality then identifies the values of
any proposed lift with the canonical lift; linear-map and intertwiner
extensionality identify the bundled maps.

More precisely, `smoothLift_unique` assumes
`(smoothInclusion rho).comp lift = f`. Evaluating this equality at `v`
gives `(lift v).val = f v`. The value of `smoothLift hSigma f` has
underlying value `f v` by its codomain-restriction definition.
`Subtype.ext`, `LinearMap.ext`, and `Representation.IntertwiningMap.ext`
therefore prove equality of the bundled intertwiners, including their
linear and equivariant structure. The factorization lemma proves the
displayed composite equation, in that order, by `ext v; rfl`.

The existence construction already proves its codomain-membership obligation:
a fixing open subgroup for a source vector fixes its image under `f` by
equivariance. The present proof uses that construction directly;
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

The original June 16, 2019 PDF was read at pages 1-2 and the
fingerprint above was verified. Page 2 supplies the open-fixing-subgroup definition
and stability of smooth vectors under the group action. Unique
factorization is an internal consequence of these constructions, rather
than a separately numbered theorem in that passage. The chapter's
stronger locally profinite, countability, and Noetherian rational-coefficient
assumptions are not used in this proof.

During preparation, the target was checked to have no changed files or
unavailable dependencies. Its target fingerprint is
`45f835d980b6814c9f6ae0fdcc0e7d13f0261fabbb3c7144dc0fd2d5795b6bb6`.
The only imported project target is this statement. Its exact transitive
definitions are the smooth-part construction
`Langlands.Representation.Smooth.SmoothPart.Definitions` and the foundation
`Langlands.Representation.Smooth.Definitions`.
At preparation, all six local dependency files matched their recorded
versions.
The proof imports only `UniversalStatement`. The pinned Mathlib
`RepresentationTheory/Intertwining.lean`, lines 51-55 and 213-223,
supplies intertwiner extensionality and the composition convention used here.

The preparation environment pinned Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The whole-target theorem retains four independent universes and introduces the
topological-group instance only at the target's internal binder. The two helper
lemmas and closing theorem belong to this one proof module.
During preparation, native compilation and assignment to the entire
proposition with four independent universes passed with exit code 0.
That check had no external topological-group instance. The inspected axiom
closures of both helpers and the closing theorem contained only `propext`,
`Classical.choice`, and `Quot.sound`. No placeholders or project axioms are
introduced. Those preparation checks were development checks only. The
proof's validation against the exact target is recorded in
[UniversalStatement](UniversalStatement.md#checks).
