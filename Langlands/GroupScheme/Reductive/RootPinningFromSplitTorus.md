# Root pinnings for split maximal tori

Author: Worker 1472.

`RootPinning.ofSplitMaximalTorus` constructs simple-root trivializations
from a split maximal torus and a supplied realized root datum and base.
For any field `k : Type u`,
an actual connected reductive group `G`, a split maximal torus inclusion
`i : T.toGrp ⟶ G`, a realized root datum `P` for `i`, and any base `b` of
`P`, it constructs `RootPinning i P b`. The field, group, torus,
inclusion, datum and base remain the supplied ones.

The constructor applies the published theorem `splitRootLieLine` to the
original field and split maximal torus. It supplies a linear equivalence
from `k` to each actual root Lie weight space. The existing constructor
`RootPinning.ofRootLines` uses the root-range equality in `IsRootDatumOf`
to see that each simple root of `b` is an actual root and selects the
corresponding equivalence by classical choice. The connected reductivity
proof supplies the affine instance required for the Lie constructions.
No finite-index or reducedness assumption on the supplied datum is
needed for this conclusion.

The accompanying theorem `Langlands.GroupScheme.rootPinningExistence`
proves the published `RootPinningExistenceStatement.{u}` by wrapping
the constructor in `Nonempty`.

The companion theorem
`splitPinningExistence_of_rootDatumExistence` has the explicit premise
`RootDatumExistenceStatement.{u}` and concludes
`SplitPinningExistenceStatement.{u}`. It applies the existing constructor
`SplitPinning.ofRootDatumExistence` and supplies its root-line input with
the same published theorem `splitRootLieLine`. That constructor chooses
a finite realized reduced root datum from the premise and uses the
published integral-base existence result to assemble a `SplitPinning`.
The returned proposition does not assert that its bundled torus equals
the initial torus witness.

Both proofs retain arbitrary universe `u` and arbitrary fields. The
weight spaces keep their defining equations on every coefficient
algebra and every torus point over that algebra. No dimension,
characteristic, perfectness or norm premise is added.

This is an internal deduction from the published root-line theorem and
pinning constructors. The source interpretation of pinnings and root
lines is recorded in the imported statement and construction Markdown;
this module makes no new literature assertion. It proves existence of
the trivializations for supplied realized root data. Its companion
theorem still assumes root-datum existence, and neither theorem
constructs pinned isomorphisms, automorphism sections, descent data,
adjoint quotients or the quasi-split inner form of the host task.
