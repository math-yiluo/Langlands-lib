# Fixed-vector detection and dimension descent

The Lean proofs in this module are by Worker 196, reused unchanged from the
public draft of the constituent-induction task. Worker 1 prepared this expanded
explanation and the separate closing theorem in `DetectionProof`.

These are internal algebraic helpers for constituent induction. Their precise
scope is specified by the six propositions in the published
`DetectionStatement` module. This module proves the helpers from Mathlib and
the published fixed-vector laws, actual smooth subquotient constructions and
compact-open fixed-vector surjectivity. It makes no claim to prove the
constituent theorem itself. The literature motivation is recorded in the
published statement's Markdown; the implemented proofs are described below.

## Generation and detection

`Langlands.eq_top_of_fixedVectors_le_of_semisimple` works over any field `R`
and any group `G`, with no topology or smoothness hypothesis. Suppose every
atom subrepresentation contains a nonzero `K`-fixed vector. For an invariant
subspace `T` containing all fixed vectors, the proof transports semisimplicity
to the module over the group algebra `R[G]`. Mathlib's
`IsSemisimpleModule.sSup_simples_eq_top` writes the whole module as the
supremum of its simple submodules. The order isomorphism between
subrepresentations and group-algebra submodules turns each simple submodule
into an atom `S`. The chosen nonzero fixed vector lies in `S ⊓ T`, so this
intersection is nonzero. Atomicity makes it equal to `S`, giving `S ≤ T`.
The supremum is therefore contained in `T`, which must be top.

`Langlands.intertwiner_eq_zero_of_fixedVectorsMap_eq_zero` assumes the
generation property directly. If the fixed-vector restriction of an actual
intertwiner `f` is zero, all fixed vectors lie in its invariant kernel. The
generation property makes that kernel top, and evaluation at every vector
shows `f = 0`. The source and target carriers have independent universes.

Neither result asserts that a subgroup satisfying its generation hypothesis
exists. Neither assumes finite-dimensional carriers.

## Two dimension comparisons

The private lemma `finrank_lt_of_injective_not_surjective` treats a linear map
into a finite-dimensional space. Injectivity first supplies finite
dimensionality of the source and a weak finrank inequality. Equality of
finranks would make injectivity equivalent to surjectivity, contradicting the
second hypothesis. This proves strict inequality.

The private lemma `finrank_lt_of_surjective_not_injective` is the corresponding
argument for a surjection from a finite-dimensional space: the target becomes
finite dimensional, and equality of finranks would imply injectivity.

## Actual kernel, image and cokernel

`Langlands.SmoothRep.finrank_fixedVectors_kernel_lt` works over any field, any
group topology and any subgroup `K`. The fixed-vector map of the actual
kernel inclusion is injective. If it were surjective, every ambient fixed
vector would come from a kernel vector, forcing the restricted endomorphism
to be zero. The assumed nonzero restriction therefore gives strict dimension
decrease by the first comparison.

The remaining three public lemmas work over `ℂ` for a topological group and
a compact open subgroup. They use
`Langlands.Compact.fixedVectorSurjectivity`: a surjective intertwiner between
smooth representations induces a surjection on these fixed spaces.

`Langlands.SmoothRep.finrank_fixedVectors_image_lt` defines a private
`rangeFactor` from the source onto the actual image, using the linear map's
`rangeRestrict`. Its fixed-vector map is surjective by the published
surjectivity theorem. The image inclusion is injective on fixed vectors. If
that inclusion were surjective, composing the two surjections would make the
ambient fixed-vector endomorphism surjective and hence injective in finite
dimension. This contradicts its assumed noninjectivity. The first dimension
comparison gives the strict decrease.

`Langlands.SmoothRep.finrank_fixedVectors_cokernel_lt` applies the published
surjectivity theorem to the actual quotient map onto the cokernel. If its
fixed-vector map were injective, the fact that it annihilates the original
endomorphism's image would force that endomorphism's fixed-vector restriction
to be zero. The assumed nonzero restriction contradicts this, and the second
dimension comparison gives the strict decrease.

Only the ambient fixed space is assumed finite dimensional in these three
lemmas. The carrier can be infinite dimensional. The kernel argument does not
require a topological group or a compact open subgroup.

## Subquotient witness

`Langlands.SmoothRep.not_injective_fixedVectorsMap_of_subquotient_witness`
starts with an injective intertwiner `i : C ⟶ A`, a surjective intertwiner
`q : C ⟶ D`, and endomorphisms satisfying `i ∘ fC = fA ∘ i` and
`q ∘ fC = 0`. The ambient fixed space is finite dimensional and the fixed
space of `D` is nontrivial.

The restriction `j` of `i` is injective, so the fixed space of `C` is finite
dimensional. The restriction `r` of `q` is surjective by compact-open
fixed-vector surjectivity. If the restriction of `fA` were injective, the
commuting equality and injectivity of `j` would force the restriction `t` of
`fC` to be injective. Finite dimension makes `t` surjective. Choose a nonzero
fixed vector `d` of `D`, lift it through `r`, and then lift that preimage
through `t`. The equality `q ∘ fC = 0` now gives `d = 0`, a contradiction.

No semisimplicity or irreducibility is assumed in this argument, and no
finite-dimensional carrier is required.
