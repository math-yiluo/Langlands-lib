# Archimedean idele invariants under restriction

This module defines `archimedeanIdeleInvariantVector`, the additive map sending
an actual degree-two idele cohomology class for `E/F` to its archimedean
invariants indexed by the infinite places of `F`. Each component is the
published `archimedeanIdeleInvariantAt`; its value is independent of the place
of `E` used to compute it. The vector assumes `E` is a number field and `E/F`
is Galois. All fields belong to the same arbitrary universe.

For a tower `F → K → E`, with `E/F` Galois and compatible algebra structures,
let `q | w | v` be infinite places of `E`, `K`, and `F`, respectively. The theorem
`archimedeanIdeleInvariant_relativeIdeleRestriction` proves

`inv(K,q)(res(x)) = inertiaDeg(v,w) • inv(F,q)(x)`.

Here `res` is the actual `relativeIdeleRestriction` on the idele representation.
Mathlib's `InfinitePlace.inertiaDeg_eq_finrank` identifies the factor with
`[K_w : F_v]` for the actual infinite completions. The theorem includes the
three compatible `LiesOver` instances and does not require `K/F` to be normal.
Only `E` has an explicit number-field hypothesis; `F` and `K` are fields with
the stated algebra structures. The theorem
`archimedeanIdeleInvariantVector_relativeIdeleRestriction` gives the same
formula for the canonical vector, requiring only `w | v`.

The implemented proof first establishes that every archimedean invariant is
killed by two: the cocycle formula takes values in zero and the class of
one half. It also establishes vanishing at an unramified infinite place,
using the triviality of its stabilizer. For a place ramified over `K`,
Mathlib supplies a complex-conjugation automorphism over `K`. Its restriction
of scalars is the same nonidentity automorphism over `F`. The coefficient
map for cohomological restriction is the identity, so the two cocycle
conjugation values agree. This proves the auxiliary theorem
`archimedeanIdeleInvariant_relativeIdeleRestriction_of_isRamified`.

If `q` is ramified over `K`, then `w` is real and `[K_w : F_v] = 1`, so the
auxiliary theorem proves the formula. If `q` is unramified over both bases,
both invariants vanish. In the remaining case `q` is unramified over `K`
and ramified over `F`; then `w` is complex above the real place `v` and
`[K_w : F_v] = 2`. The left side vanishes and the right side vanishes by
two-torsion. Finally, a place `q` above `w` exists by algebraicity; the
published independence theorem identifies the fixed-place formula with
the canonical vector formula.

This is an internal derivation from the published archimedean cocycle,
cohomology restriction, and place-independence constructions, together with
Mathlib's infinite-place ramification and completed-degree API. It assumes
no reciprocity law or invariant formula. It does not prove the sum formula,
construct global invariants on idele-class cohomology, or complete
`GlobalInvariantStatement`.
