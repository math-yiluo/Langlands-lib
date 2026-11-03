# Relative Tits nondegeneracy from actual nontrivial simple-root points

This internal supporting unit isolates the remaining rational-point existence
input in the Tits nondegeneracy axiom. `RelativeSimpleRootPointData i ν` consists
of an actual nonidentity rational point in each actual simple-root subgroup
functor. The structure is input data; its existence is not asserted.

For a split torus, a relative reflection in an actual root sends that character
to its negative. This follows from the action on the rational root vector and
injectivity of rationalization of the split character lattice.

Take any normalizer representative of the reflection in a simple positive root
`a`, and a nontrivial point `b` of `U_a(k)`. The direct positive-root inclusion
places `b` in the minimal standard parabolic. Actual normalizer conjugation
places `n b n⁻¹` in `U_{-a}(k)`. The pairing of `-a` with `-ν` is positive, so
this conjugate lies in the dynamic unipotent subgroup for `-ν`. Negating `ν`
is the same as inverting its Gm parameter. If the conjugate also lay in the
minimal standard parabolic, its unconditional inclusion in the dynamic
parabolic for `ν` and the proved opposite-intersection theorem would force
`n b n⁻¹ = 1`, hence `b = 1`, a contradiction.

Thus the actual point data proves the full `conj_not_le` field for every simple
reflection and every normalizer representative. The argument assumes no
genericity, Bruhat decomposition, Coxeter system, rank-one normalizer
factorization, or full standard-parabolic point theorem. The split torus and
actual nontrivial root points remain explicit inputs. Their needed existence,
and the full `RelativeTitsSystemStatement`, remain separate proof obligations.
