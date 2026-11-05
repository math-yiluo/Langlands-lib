# Finite covariant functions on a proper homogeneous quotient

This internal construction restricts the Library's character-line-bundle section
comparison to the field scalars supplied by the actual structure maps. It proves
finiteness of the entire space of all-test right-character-covariant regular
functions when the supplied homogeneous quotient is proper. Its provenance is
the existing homogeneous character descent construction and the proved proper
coherent cohomology theorem.

The field `k` and all schemes lie in the arbitrary universe `u`. The inputs are
actual group schemes `H` and `G` over `Spec k`, a morphism `i : H ⟶ G`,
a supplied `HomogeneousQuotient i`, written `D`, and an actual rational
character `χ` of `H`. Write `Q` for its quotient scheme and `q : G → Q`
for its projection. Construction of the function subspace requires `i` to be
monomorphic. The section equivalence and finiteness also require `G → Spec k`
to be affine.

`structureRingHom_projection` proves that the field structure map to
`Γ(Q, ⊤)`, followed by pullback along `q`, is the field structure map to
`Γ(G, ⊤)`. It follows directly from `q` being a morphism over `Spec k`
and functoriality of global-section pullback. `projection_field_smul` identifies
the resulting restricted scalar action on `Γ(q_*𝒪_G, ⊤)` with the ordinary
field action on the actual algebra `(algΓ k).obj G.X`. These objects have the
same underlying global functions on `G`; the lemma checks their scalar actions.

`rightCharacterCovariantSpace` is a `k`-submodule of that actual global-function
algebra. Its carrier contains exactly every function `f` satisfying
`IsRightCharacterCovariant i χ f`: on every relative scheme test `T`,
for every `a : T → G` and `b : T → H`,

`f(a · i(b)) = χ(b) · f(a)`.

Values here are global-section pullbacks, and `χ(b)` is the actual unit
`characterEval χ T b`. No density or restriction to field-valued points is used.
Closure under addition and field scalars follows from the existing
`Γ(Q, ⊤)`-submodule and the proved equality of scalar actions.

`characterFieldSectionsEquiv` is a `k`-linear equivalence between the relative
global sections of the actual `characterLineBundle i D χ` and this entire
subspace. Both maps preserve the underlying function. The two directions of the
existing cocycle-section comparison supply membership, and
`projection_field_smul` proves field linearity.
`characterFieldSectionsEquiv_apply` records the underlying-function equality.
This equivalence requires no properness.

With `IsProper Q.hom`, `finite_characterFieldSections` applies
`properCoherentCohomologyFinite` to the actual character line bundle.
Its local rank-one property supplies quasi-coherence, and
`hasFiniteAffineSections_lineBundle` supplies finite sections on every affine
open. Degree-zero cohomology is therefore finite over `k`, and
`relativeCohomologyZeroIso` transports this result to its global sections.
Finally `finite_rightCharacterCovariantSpace` transports finiteness through
`characterFieldSectionsEquiv`. It concerns the whole subspace, including the
possible zero space, and uses no additional smoothness assumption on `Q`.

Properness of the supplied quotient remains an explicit hypothesis.
The construction does not choose a Borel subgroup, prove Borel properness,
construct a regular representation, select a dominant character, or prove a
Steinberg or conjugation-map result. Those obligations remain separate.
