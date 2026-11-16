# Block Fourier multipliers under normalized induction slices

Module: `Langlands.Representation.Archimedean.RealBlockMultiplierSlices`.
Namespace: `Langlands.Archimedean.RealBlockMultiplierSlices`.

This is internal infrastructure for transferring local Fourier landing results to
consecutive coordinates in an ambient real general linear group. Its landing
lemma explicitly assumes the local result. It does not construct recurrent
multipliers, prove any local landing theorem, or prove the induced-block swap.

The selected definition `twoStep n p q D E μ ν f` applies the finite normalized
Fourier multiplier on rotation `p` with window `[-D,D]` and sequence `μ`, then
that on rotation `q` with window `[-E,E]` and sequence `ν`. Both are the finite
sums defined in `RealDisjointBlockMultipliers.finiteMultiplier`. No continuity,
recurrence, disjointness or symmetry is required to define this function.

Let `a+r≤n` and use the published normalized slice

`σ_κ f(g) = ν_(n,a,r)(g) f(ι(g)κ)`,

where `ι` embeds `GL_r(ℝ)` on coordinates `a,...,a+r-1` and
`ν_(n,a,r)(g)=|det(g)|^(-((n-r)/2-a))`. The normalizing function in this formula
is unrelated to the multiplier sequence named `ν` above.

For `p+1<r`, `finiteMultiplier_slice` proves that the finite multiplier along
`p` of `σ_κ f` equals `σ_κ` of the ambient finite multiplier along `a+p`, with
the same window and sequence. This is an equality on all of `GL_r(ℝ)`, for
arbitrary `f` and `κ`. It follows by the published exact Fourier coefficient
formula for a slice and finite-sum distribution of the common normalizing
factor. `twoStep_slice` applies this identity twice; it requires both rotations
to be contained in the slice and does not require them to be disjoint.

`multiplier_relation_slice` transfers a compact Fourier identity
`Φ^(a+p)_j H = μ(j) Φ^(a+p)_j f` on `O(n)` to
`Φ^p_j (σ_κ H) = μ(j) Φ^p_j (σ_κ f)` on `O(r)`, for `κ∈O(n)`. Indeed,
`ι(g)κ∈O(n)` when `g∈O(r)`, and the normalizing factor is the same on both
sides. This lemma does not require continuity.

Finally, `twoStep_landing_in_stages` takes a supplied local implication at rank
`r`: for every right `O(r)`-finite source vector in the standard module of
`ds`, and every pair of continuous intermediate and output functions whose
compact Fourier coefficients are related by the multipliers `μ` along `p`
and `ν` along `q`, the output coefficients along `t` vanish for `|j|<L` on
`O(r)`. It retains that local implication as an explicit premise.

For arbitrary lists `pre,post` with `realRank pre=a` and `realRank ds=r`,
an ambient right `O(n)`-finite source vector in the standard module of
`pre ++ ds ++ post`, and smooth ambient intermediate and output functions
satisfying the two corresponding identities on `O(n)`, the lemma concludes
vanishing of the output coefficients along `a+t` for `|j|<L` on `O(n)`.
The hypotheses include `a+r≤n` and containment of all three local rotations;
there is no suppressed rank or nonzero-weight condition. The intermediate
and output functions need no ambient standard-module membership.

The proof takes the normalized slice at each `κ∈O(n)`. Published induction
slicing gives source standard-module membership and right orthogonal
finiteness, and smoothness gives continuous slices of the other two functions.
The preceding multiplier relation lemma transfers both identities. Apply the
supplied local implication and evaluate its conclusion at the identity of
`O(r)`. The slice factor there is one, giving the desired coefficient at `κ`.
Only compact vanishing is concluded; extending it to all ambient group points
requires any relevant principal-series hypotheses in a separate application.

All provenance is internal. The results follow from finite sums and the
published `RealInductionStagesSlice` identities and preservation lemmas, with
no new external mathematical result assumed.
