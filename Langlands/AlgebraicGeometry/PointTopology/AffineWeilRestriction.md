# The affine Weil-restriction point homeomorphism

Worker 105 implements the point comparison of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 2.4,
printed page 3. The continuous-function proof below is a derived reformulation
of the source's finite projective coordinate argument.

## Rings, schemes and independent topologies

The rings `A` and `B` are arbitrary commutative rings, and `B` is a finite
projective `A`-algebra. They are topological rings, with `B` carrying its
canonical module topology `IsModuleTopology A B`. The explicit topological-ring
structure on `B` imposes no further condition: Mathlib supplies it from the
module topology for a finite algebra. The coordinate algebra `C` is only finite
type over `B`. Finite presentation, Noetherianity, locality, a field, separation,
faithfulness and freeness are not assumed.

`weilRestrictionAlgPointEquiv` evaluates the constructed representing
bijection of `Langlands.Algebra.WeilRestrictionFiniteType A B C` at the test
algebra `A`, then composes with the canonical tensor-unit isomorphism
`B ⊗[A] A ≃ₐ[B] B`. The theorem
`weilRestrictionAlgPointEquiv_toAlgHom` identifies this forward map explicitly.
Both point carriers have their previously defined evaluation topologies;
neither topology is defined by transporting the other along this bijection.
`weilRestrictionAlgPointHomeomorph` proves that the bijection is a
homeomorphism for these topologies. The algebra-point construction permits
independent ring universes.

`weilRestrictionSpecPointHomeomorph` transfers this exact comparison to the
actual scheme morphisms `Spec A → Spec W` over `Spec A` and
`Spec B → Spec C` over `Spec B`, where `W` is the constructed representing
algebra. Its apply theorem identifies the map with the algebra-point
bijection. `weilRestrictionRingPointHomeomorph` uses the existing actual
morphism carriers in `Over (Spec _)` and their global-section evaluation
topologies. The previously proved spectrum/global-section comparisons
identify these topologies with the spectrum point topologies. These scheme
constructions use the common universe of Mathlib's scheme category.

For an arbitrary actual affine scheme `X` over `Spec B`, assume its structure
morphism is locally of finite type. The existing
`affineCoordinate_finiteType_iff` gives finite type of its actual global-section
algebra; affineness supplies quasi-compactness, hence this is exactly the
source's affine finite-type case. `affineWeilRestriction A B X` is the actual
scheme `Spec W` over `Spec A`, formed from that global-section algebra. Its
affineness and local finite type are instances, and
`affineWeilRestriction_quasiCompact` proves quasi-compactness.
`affineWeilRestrictionPointEquiv` gives its representing equivalence on every
actual affine test scheme `Spec T`, with target the actual points of `X` over
`B ⊗[A] T`. No topology on `T` is assumed for this equivalence. It is composed
of the existing affine scheme/algebra equivalences and the algebraic
representing equivalence.

`affineWeilRestrictionPointHomeomorph` gives the canonical homeomorphism
between the actual `A`-points of this scheme and the actual `B`-points of `X`.
The apply theorem states that its map is precisely the representing
algebra-point bijection in global-section coordinates. The scheme topologies
come from the existing affine evaluation construction, independently of Weil
restriction. No chosen presentation of `X` is an input. On finitely presented
coordinate algebras the imported `finitePresentationAlgEquiv` and its
universal-point and all-test-algebra compatibility theorems compare this
representing algebra with the published TauCeti Weil restriction.

## Implemented proof

`AlgPoint.continuousEvaluationAlgHom` is the actual algebra homomorphism
sending a coordinate to its continuous evaluation function. It packages the
universal continuous family of algebra points.

Forward continuity of the canonical point bijection follows by tensor
induction on each value of the universal point. Evaluation of a pure tensor
is a continuous scalar multiple of a fixed element of `B`, and evaluation
commutes with addition. The universal property of the evaluation topology
then proves continuity into the `B`-valued point space.

For inverse continuity, use the constructed continuous-function tensor
isomorphism

`B ⊗[A] C(Y,A) ≃ₐ[B] C(Y,B)`

with `Y = AlgPoint B C B`. Compose its inverse with the continuous evaluation
family and classify the resulting tensor-valued point by representability.
This constructs `weilRestrictionContinuousPoint`, an actual algebra map
`W →ₐ[A] C(Y,A)`. Naturality of the algebraic representing equivalence and
evaluation compatibility of the tensor-function isomorphism show that
evaluating this family at every `q : Y` produces the inverse canonical point.
Thus each coordinate of the inverse is a continuous function. The forward
and inverse continuous maps give the homeomorphism, and composition with the
existing spectrum and affine-scheme homeomorphisms gives the actual scheme
versions.

The proof needs no compactness hypothesis on `Y`. The source's separate
assertion that `A` inherits its topology from an injective finite locally free
extension additionally uses faithfulness; that assertion is covered by the
separate finite-algebra splitting result. This contribution proves the affine
point comparison without using that assertion. Explicit Weil-restriction
functoriality and preservation of closed immersions, and extension of the
representing equivalence from affine test schemes to all test schemes, remain
separate parent-task obligations. It makes no whole-paper completion claim.
