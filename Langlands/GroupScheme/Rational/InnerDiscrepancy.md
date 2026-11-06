# Natural inner discrepancy cocycles from faithful actions

Author: Worker 1472.

This is an internal construction from the existing actual automorphic action,
local group isomorphism and full-centre adjoint quotient interfaces. It does
not assert quasi-split inner-form existence. Its provenance is the intrinsic
uniqueness of an inner automorphism's adjoint representative, followed by
composition and pullback of local equivalences.

`AutomorphicAction.IsFaithful` tests equality of acting points after every
refinement of a relative test scheme and on every group point there. It is
stronger than inspecting the action only on the original test's points.
`isFaithful_of_kernel` reduces this condition to triviality of the kernel by
acting with the ratio of two points.

`IsAdjointQuotient.innerAction_kernel` proves that the actual inner action has
trivial kernel. An adjoint point lifts along the given quotient after an fpqc
base change. If its action is trivial on all refinements, the lift commutes
with every group point on every further refinement, so it belongs to the full
scheme-theoretic centre. Its quotient image is the identity. Equality descends
along the fpqc cover by `hom_ext_of_local_quotient_lift`. This argument uses the
actual central kernel, including any nonsmooth centre; no global lift of the
original point is assumed. `innerAction_isFaithful` applies the kernel reduction.

For local multiplicative equivalences `e_b : G → H`,
`RepresentsDiscrepancy a b c x` means
`e_(t b)(a(t x,g)) = e_(t c)(g)` for every refinement `t` and group point `g`.
`HasInnerDiscrepancy` asserts existence of such an acting point for every test
and pair of cover points. No choice of a natural family or cocycle is required.
Pullback preserves representing points. Faithfulness makes them unique, since
the local equivalences are injective. Composition of discrepancies is their
product, in the order `x_(b,d) = x_(b,c) * x_(c,d)`.

`innerCocycle` chooses each representative, then derives naturality by
uniqueness after pullback and the cocycle identity by uniqueness after
composition. `innerCocycle_hasDiscrepancy` recovers the original equation using
the identity refinement. `innerCocycle_unique` uses the naturality of any other
cocycle with the discrepancy equation to identify all its values with these
representatives.

`QuasiSplitInnerForm.ofInnerDiscrepancy` uses these results to construct the
natural adjoint-valued cocycle and assemble the existing presentation. It still
requires a quasi-split ground-field model and adjoint, their actual quotient,
a finite Galois field extension in the same universe, and the natural local
multiplicative equivalences with inner discrepancies. Those are explicit
premises of this helper, not conclusions or extra premises of the unchanged
`QuasiSplitInnerFormExistenceStatement`. No unconditional proof of that
statement, no pinning, and no model or quotient existence is supplied here.
