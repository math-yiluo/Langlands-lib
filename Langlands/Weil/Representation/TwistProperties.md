# Shared properties of scalar character twists

Worker 111 extracted this common interface from the published
`Langlands.VirtualRepresentation.ExactTwist` (Worker 20) and
`Langlands.Weil.Representation.TwistClasses` (Workers 4 and 62).
Worker 21 compared the original full elaborated declarations and checked the
affected consumers. This is an internal consolidation of existing constructions
and intrinsic laws, not a new independent mathematical statement.

The shared module depends only on the existing finite-representation twist,
continuity predicates, operation-closure proof, and scalar-twist algebra proof.
Neither genuine class twists nor exact virtual twists depends on the other.
The two original module import paths are preserved.

## Preserved constructions and proofs

For an arbitrary field `K`, group `G`, and character `chi : G →* Kˣ`,
`rank_twist` is proved by reflexivity because twisting retains the vector space.
Its `simp` attribute is retained. `twistOneEquiv` and `twistMulEquiv` rewrite
the actual representation by the published `Langlands.twist_one` and
`Langlands.twist_twist`, respectively, then apply the reflexive representation
equivalence. They are genuine invertible intertwiners on the original carrier.

The coefficient, group, and representation-carrier universes are independent,
in that order. The source expressions are copied from `ExactTwist`; Lean
introduces the carrier universe automatically, just as before. `Field K` and
`Group G` remain the only algebraic instances in these telescopes.

`isContinuous_twist` takes a group with a topology, a continuous character
`chi : G →ₜ* ℂˣ`, an implicit finite complex representation `A`, and a proof
of `A.IsContinuous`. It applies the existing
`Weil.OperationClosure.continuous_twist` to the character's continuity proof.
The group and carrier universes remain independent. No continuity assumption
on the group operations is introduced, and the published usual complex
endomorphism topology is unchanged.

## Callable interface and migration

Every name below has namespace prefix `Langlands.FiniteRepresentation`.

| Original call | Shared call |
| --- | --- |
| `rank_twist chi A` | `rank_twist chi A` |
| `twistOneEquiv A` | `twistOneEquiv A` |
| `twistMulEquiv chi eta A` | `twistMulEquiv chi eta A` |
| Exact/spectral: `isContinuous_twist chi hA` | `isContinuous_twist chi hA` |
| Class-only: `isContinuous_twist chi A hA` | `isContinuous_twist chi (A := A) hA` |

Only `continuousIrreducibleTwist` in `TwistClasses` required a call-site edit:
its representation is inferred from `A.property.1`. The exact and spectral
callers already use the implicit representation argument. No declaration is
renamed. Explicit universe instantiation retains the same parameter order.

At repair base `f8488ce760fd0ec518e405f24e33da3f8aaf7ef2`, the transitive
affected import closure consists of the two corrected modules and
`Langlands.LocalFactor.SpectralTwist`,
`Langlands.Weil.Representation.CharacterLine`,
`Langlands.LocalFactor.RankOne`, and
`Langlands.VirtualRepresentation.Weil.Twist`.

## Provenance

The original paired Markdown in `ExactTwist` retains its Tate citation and
explains its derived algebraic generalization. `TwistClasses` retains its
internal-construction rationale and attribution to Workers 4 and 62.
This extraction adds no literature claim. Its four bodies are the published
`ExactTwist` bodies without mathematical changes. Comparison of the original
Lean elaborations found that the class-side bodies and types agree after
renaming the carrier universe, except for the explicit versus implicit `A`
binder in continuity. Private Lean probes check the complete unapplied
telescopes, definitional agreement with the original bodies, and standard
axioms; independent review and Library publication remain required.
