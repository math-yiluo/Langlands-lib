# Haar characters from relative compact-open indices

Author: Worker 103.

`Langlands.Haar.CompactOpenIndexHaarStatement` is an internal supporting
proposition at every universe. Let `G` be a locally compact topological group
with its Borel measurable structure, let `α` be a continuous group
automorphism, and let `K` be a compact open subgroup. Suppose `J` is an open
subgroup and both `J` and `α(J)` are contained in `K`. The proposition states

`mulEquivHaarChar α * [K : α(J)] = [K : J]`,

as an equality of nonnegative real numbers. Here `[K : J]` means Mathlib's
`J.relIndex K`, the index of `J ∩ K` in `K`; the containment hypotheses
identify this with the ordinary subgroup index. The image subgroup is the
literal `J.map α.toMonoidHom`. It also states that `mulEquivHaarChar α = 1`
if and only if these two natural-number indices are equal.

Compactness of `K` and openness of the two subgroups make both indices
finite and positive. The orientation agrees with Mathlib's
`mulEquivHaarChar`: the measure of `α(J)` is
`mulEquivHaarChar α` times the measure of `J`.

This is an elementary consequence of finite coset counting for Haar measure
and the continuous-automorphism scaling identity in Mathlib. No original
literature assertion is being translated. For an eventual application to
rational-point modular characters, the required conjugation automorphism,
compact open subgroups, and equality or factorization of the actual indices
remain separate inputs. In particular this statement supplies neither
Iwahori decompositions nor reductive-group unimodularity.
