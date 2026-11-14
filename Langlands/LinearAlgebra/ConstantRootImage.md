# Constant squared lengths of linear images of roots

Let `P : RootPairing ι ℚ M N` be irreducible. For a rational linear map
`f : M →ₗ[ℚ] E` and a rational bilinear form `C` on `E`, the proposition
`HasConstantRootImageLength P f C` says that there is a nonzero rational
number `d` such that
`C (f (P.root i)) (f (P.root i)) = d` for every root index `i`.
The definition does not require `C` to be symmetric or positive definite.

If `C` is symmetric and `P` is a root system, so that its roots and coroots
span the respective spaces, `injective_of_hasConstantRootImageLength`
proves that `f` is injective. The same symmetric-form hypothesis implies
that the full pairing `P.pairing` is symmetric; this latter conclusion does
not require the additional root-system spanning instance. These statements
do not require finiteness, crystallographicity or reducedness.

The proof first establishes that two roots in an irreducible rational root
pairing have a root pairing nontrivially with both. For a prescribed root
`a`, span the roots pairing nontrivially with `a`. If a root outside this
span paired nontrivially with one of its generators, reflection in that
generator would produce another generator and put the outside root in the
span. The span is therefore the whole root space by Mathlib's
irreducibility lemma. If every generator were orthogonal to a second root
`b`, this span would lie in the kernel of the coroot of `b`, while also
containing the root `b`, contradicting its self-pairing two.

For a symmetric rational bilinear form `B` taking the common value `c` on
the self-pairing of every root, expand the self-pairing of a reflected root.
When the corresponding root-coroot pairing is nonzero, cancellation gives
`2 * B (P.root j) (P.root i) = P.pairing j i * c`. For an orthogonal pair
of roots, choose a root nonorthogonal to both. Apply the same identity to
that root and its reflection in one of the two original roots; subtracting
the resulting identities gives the missing zero cross-term. Thus the
formula holds for all pairs of roots.

If `P` is a root system, equality on the spanning roots extends the formula
to the identity of linear forms
`2 • B (P.root i) = c • P.coroot' i`. Apply this to the pullback
`B = C.compl₁₂ f f`. For a vector in the kernel of `f`, nonvanishing of
`c` forces all its coroot evaluations to vanish. Coroot separation then
makes that vector zero. Symmetry of the full pairing follows separately
from the formula on root pairs and cancellation of `c`.

This is an internal auxiliary construction, derived from Mathlib's
root-pairing reflection identities, irreducibility and spanning lemmas.
It supports a possible folding argument for the quasi-split splitting
criterion. It supplies no comparison between actual absolute and relative
roots of an algebraic group, no group-theoretic splitting theorem, and no
proof of the local anisotropic affine-diagram statement.
