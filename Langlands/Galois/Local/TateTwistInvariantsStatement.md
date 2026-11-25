# Tate's invariants of the completed algebraic closure and its twists

`TateTwistInvariantsStatement` fixes a prime `p` and a finite extension
`F` of `ℚ_p`. It uses the actual completed algebraic closure `C_F`
with its continuous absolute Galois action and the chosen embedding
of `F`. The fixed field is the image of `F`. A fixed vector for the
twisted action `x ↦ χ_cyc(σ)^j σ(x)` is zero for every nonzero integer `j`.

Tate's theorem for the cyclotomic power applies after a finite base
extension in the field fixed by its kernel. At that stage the
extension is totally ramified and its remaining Galois group is
isomorphic to `ℤ_p`. Both the image of the field and the action on the
completion are those of the Library's spectral-norm construction.
The statement uses only degree-zero invariants.

The twist vanishing distinguishes the graded pieces of a labelled
Hodge–Tate representation. The fixed-field equality identifies their
scalar field and makes finite Galois descent of the labelled pieces
available for the rational-model argument.

## Source

J. Tate, *p-Divisible Groups*, in *Proceedings of a Conference on Local
Fields*, Springer, 1967, §3.3, printed p. 176, Theorems 1 and 2,
using Propositions 8 and 10, pp. 174–175. The second theorem is
specialized to a nonzero power of the cyclotomic character. Registered
`tate-1967-p-divisible-groups`, SHA256
`720bf7128d4f048853435b083d18d0d863056c1f991942192a7f00daa7e424aa`.
