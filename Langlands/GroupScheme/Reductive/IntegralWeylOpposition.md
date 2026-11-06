# Integral Weyl opposition for rho

This internal argument constructs a Weyl element sending the published
integral weight rho to its negative. The input is a finite reduced root
datum over the integers, a supplied base, and full integral coroot span.
The weight and coweight groups and the root index type may have independent
universes. The proof stays in the integer lattices.

The coroot span hypothesis makes the action of root-datum automorphisms
on the finite root index set faithful: equal permutations give equal
coweight maps on every coroot, hence on the entire coweight group, and
the perfect pairing determines the automorphism. Thus the automorphism
and Weyl groups are finite.

The canonical root form is a sum of products of integral coroot
evaluations. Each root has strictly positive squared norm. The existing
polarization identity shows that twice its pairing with a weight equals
the squared root norm times the corresponding coroot evaluation.
In particular its pairing with rho is positive on every simple root.

Choose a Weyl translate `x` of rho minimizing its canonical pairing
with rho. Comparison with each left simple reflection gives a
nonpositive value of `x` on every simple coroot. Weyl transport preserves
coroot regularity, and the evaluations are integers, so those values
are at most minus one.

To identify this translate, first consider any weight `x` with these
simple-coroot bounds. The weight `x + rho` has nonpositive simple-coroot
values. The polarization identity and positive squared simple-root
norms imply nonpositive canonical pairings with the simple roots.
Every positive root is a nonnegative integral combination of them, so
the same holds for all positive roots. The published formula expressing
twice rho as the positive-root sum then gives a nonpositive pairing of
rho with `x + rho`. If `x` has the same squared norm as rho, bilinearity
identifies the squared norm of `x + rho` with twice that last pairing.
It must be zero because the canonical form is a sum of squares.
The form's kernel criterion, the polarization identity, and the full
simple-coroot basis force `x + rho = 0`.

The canonical form is Weyl invariant, so the chosen minimizing translate
has the required norm. This proves `exists_weyl_neg_rho`, and
`opposition` chooses an actual Weyl element together with this
certificate.

No group scheme, maximal torus or root datum is constructed by this
argument. Lifting the Weyl element to an actual normalizing rational
point and identifying conjugate dynamic parabolics remain separate
steps in the Steinberg big-cell task.
