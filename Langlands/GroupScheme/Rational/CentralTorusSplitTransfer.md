# Split-part transfer through the central torus of a represented centralizer

Authors: Worker 1348 and Worker 1361.

This is an internal, conditional assembly result over arbitrary fields, with
universe parameter `u`. Its inputs include an ambient maximal split torus and
an actual closed representative of its all-test centralizer. It asserts no
existence of rational Levi subgroups or radicals and does not prove
`MinimalParabolicTorusSplitPartStatement`.

Let `b : B → G` be a closed torus, and let `j : M → G` be a closed representative
of its whole-group centralizer. Let `z : Z → M` be closed, with commutative
source, and suppose its image contains every closed central torus of `M`.
Suppose also that `i : Z → T` and `t : T → G` satisfy `i ≫ t = z ≫ j`.
The lemma `exists_factor_through_torus_of_centralizer_center` constructs a
homomorphism `bT : B → T` satisfying `bT ≫ t = b`.

The proof uses `torusCentralizerFactor` from
`Rational.TorusCentralizerFactorization` to factor `b` through `M`.
That factor is closed and central on every test scheme and every refinement.
The assumed containment property of `z` therefore places its image inside
`range z`. Closedness of `z` makes it a monomorphic representative of its own
range. The published represented-subgroup factorization constructs `B → Z`;
composing with `i` gives `bT`, and the commuting diagram proves its composite
identity. Neither a rational-point containment argument nor a density hypothesis
is used. The lemma does not require `z` itself to be a torus or central: its
explicit containment property and closedness suffice.

The theorem
`IsMaximalSplitTorus.ambient_transfer_of_centralizer_center` additionally assumes
that `G` is affine and locally of finite type, that `t` is closed, that `b` is
ambient maximal split, and that `range j` lies in a subgroup functor `F`.
For any maximal split subtorus `a` of `T`, it proves ambient maximality of
`a ≫ t` and `torusCentralizer (a ≫ t) ≤ F`.
The split source `B` is a torus by the published `IsSplitTorus.isTorus`.
The preceding factorization supplies `bT`, and the ambient transfer
in `Rational.TorusSplitPartTransfer` gives the conclusion.

`CentralTorusSplitTransferStatement` is the Prop-valued uniform formulation;
`centralTorusSplitTransfer` proves it using the preceding theorem. The explicit
universal property for `z` can be supplied by
`IsLargestCentralSubtorus.greatest` when that interface is available.
This module does not assume or prove that any particular parabolic has these
data. Those geometric existence and comparison results, and their application
to the unchanged minimal-parabolic target, remain separate obligations.

The provenance is internal. Worker 1348 authored the Lean argument and this
documentation. Worker 1361 contributed the proposed rational-Levi and largest
central-subtorus interfaces motivating the assembly. The proof itself uses only
the existing actual-morphism factorization, centrality, split-torus and ambient
transfer APIs.
