# Character line bundles on actual homogeneous quotients

This is an internal construction from the Library's actual homogeneous quotient,
rational-character evaluation, and effective unit-cocycle descent. It supplies a
line bundle and identifies all of its global sections with the entire module of
character-covariant regular functions. It is a prerequisite for the induced-module
step of the conjugation-map task, rather than a proof of that task's proposition.

The base is an arbitrary scheme `S` in universe `u`. The inputs are actual group
schemes `H` and `G` over `S`, a morphism `i : H ⟶ G`, and a
`HomogeneousQuotient i`, denoted `D`. This structure includes an actual quotient
scheme `Q`, a smooth surjective projection `q : G → Q`, separatedness of `Q`
over `S`, and the exact right-coset fiber criterion on every relative scheme
test. The naturality and section-comparison results require that `i` be
monomorphic. The line-bundle construction also requires `G → S` to be affine.
The quotient structure's other finiteness data are retained without being used
to assert properness or finite-dimensionality here.

`subgroupDifference` chooses the subgroup point lifting `a⁻¹b` for points with
equal quotient images. Monomorphy makes the choice unique and proves naturality
under precomposition. The triple identity follows from
`(a⁻¹b)(b⁻¹d) = a⁻¹d`. For an actual rational character `χ : H → 𝔾_m`,
`characterCocycle` evaluates `χ` on this difference. It is defined on all
underlying scheme maps with equal quotient composites. Their common base map
turns the source into a relative test scheme. The lemma
`characterCocycle_on_over` compares this construction with any supplied relative
test by an identity map of underlying schemes. Cancellation proves naturality,
and multiplicativity of character evaluation proves the cocycle triple identity.

`isAffineHom_projection` proves that `q` is affine: the composite `G → Q → S`
is affine and `Q → S` is separated. The proved unit-cocycle local-units theorem
then makes the actual cocycle subsheaf of `q_*𝒪_G` locally free of rank one.
`characterLineBundle` is this sheaf with its line-bundle structure, and
`characterLineBundleTrivialization` is its pullback isomorphism to `𝒪_G` supplied
by effective descent.

`IsRightCharacterCovariant i χ f` means, on every relative scheme test `T`,
for every `a : T → G` and `b : T → H`,

`f(a · i(b)) = χ(b) · f(a)`.

Here each value of a regular function means pullback of its global section to
`T`, and `χ(b)` is the actual unit obtained from `characterEval`. The theorem
`isCocycleSection_top_iff` proves that this condition is equivalent to the
cocycle-section condition over the whole quotient. In one direction, apply the
section condition to a point and its subgroup translate; their subgroup
difference is exactly the translating point. Conversely, every equal-coset pair
is such a translate by its subgroup difference. The Library's
`IsCocycleSection.of_top` extends the equation on whole source schemes to all
open subsets, using naturality of the cocycle.

`rightCharacterCovariantSubmodule` contains every regular function satisfying
this equation. Its scalars are `Γ(Q, ⊤)`, acting through pullback along `q`; its
ambient module is the actual global sections of `q_*𝒪_G`, whose elements are
regular functions on `G`. Closure under addition and scalar multiplication
follows from the equivalent cocycle-section condition.
`characterSectionsEquiv` is a `Γ(Q, ⊤)`-linear equivalence from the global
sections of `characterLineBundle` to this entire submodule. Both directions
preserve the underlying regular function definitionally;
`characterSectionsEquiv_apply` records agreement with
`characterSectionFunction`.

No properness, finiteness of this whole module, dominance, reductivity, or
Steinberg-module theorem is assumed or proved. Restriction of scalars to a field,
proper-quotient finiteness, the actual regular group action, and the later
Steinberg and tensor-square steps remain separate obligations.
