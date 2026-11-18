# Canonical character braids inside arbitrary ambient blocks

This derived internal unit transfers the conditional canonical mixed
three-character braid to consecutive character blocks in arbitrary surrounding
standard modules, including rank four. The full normalized compact polynomial
braid remains an explicit premise.

The general helper `sliceK_frob` compares actual normalized induction-stage
slices. Let `pre`, `ds`, `es`, `post` be block lists, with `pre` of rank `a`
and `ds,es` of rank `r`, and suppose `a+r ≤ n`. Supply actual local Frobenius
data from `ds` to `es` at position `p`, and actual ambient data from
`pre++ds++post` to `pre++es++post` at position `a+p`, with the same parity,
symmetry and multiplier. For every compact right coset, slicing the ambient
output equals the local map applied to the sliced input.

The proof compares every block Fourier coefficient on the local compact
subgroup. The published slice formula identifies it with the ambient
coefficient at the embedded compact point. The normalizing slice factor
equals one there. The actual ambient and local Frobenius laws therefore
give the same coefficient, and Fourier uniqueness in the actual local target
standard module proves equality. This helper works in arbitrary local rank;
it makes no recurrence or Lie-intertwining assumption.

`ambient pre post a b c` is `pre++[a,b,c]++post`. The rank lemmas prove
that every permutation has the same ambient rank and that the three positions
fit inside it. `data0`, `data1`, `swap0`, and `swap1` construct the actual
canonical mixed crossings at positions `realRank pre` and `realRank pre+1`.
Their choices and signs are exactly those of
`RealCanonicalCharacterBraid.Choice`.

`leftWord` and `rightWord` are the actual ambient three-crossing maps from
`pre++[a,b,c]++post` to `pre++[c,b,a]++post`. Applying `sliceK_frob` at
each crossing proves `slice_leftWord` and `slice_rightWord`: the slice of
each ambient word is its proved rank-three word applied to the initial slice.
Under the full polynomial premise and the parameter sum condition, the
rank-three canonical braid makes these slices equal at every compact right
coset. Evaluation at the local identity gives equality of the ambient outputs
at every compact point. Injectivity of principal-series compact restriction
then gives equality of the actual ambient maps (`braid_of_polynomial`).

`RealAmbientCanonicalCharacterBraidStatement` packages precisely this
conditional identity in all ambient ranks and surrounding block lists.
`realAmbientCanonicalCharacterBraid` proves it.

There is also a coefficient-level interface for comparing formulas whose
intermediate functions lie in other realizations. `FourierStep p mu f g`
means that the block coefficients of `g` equal `mu(j)` times those of `f`
at every compact point. `fourier_eqOn` shows compact equality preserves those
coefficients, and `eqOn_of_fourier` reconstructs continuous compact-finite
functions from them. The helper `step_eqOn` identifies any such step with
the actual canonical crossing on compact points.

In `functional_braid`, seven continuous right-compact-finite ambient functions
satisfy the six explicit `A,C,B` and `B,C,A` multiplier steps. Only the initial
function must belong to the indicated ambient three-character source module;
the intermediate functions need not belong to the same character models as
the explicit crossings. Stepwise Fourier reconstruction identifies both
final functions with the two actual ambient words. The conditional braid
therefore proves that the two final functions agree on the ambient compact
subgroup. This interface retains all six Fourier relations and the initial
module membership as explicit inputs.

The provenance is the published normalized induction-stage slice and Fourier
formula, actual Frobenius multiplier laws, compact Fourier reconstruction and
the proved conditional rank-three canonical braid. Worker 769 supplied upstream
polynomial and scalar-degeneration inputs. This unit proves no unrestricted
polynomial braid, equality with a previously chosen interlaced equivalence,
or GL4 filtration kernel-image containment. Arbitrary multiplier parameters
give compact-equivariant maps; Lie intertwining requires additional recurrence
conditions and is not claimed here.
