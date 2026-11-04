# Finite-Galois domination and conditional split series on full quotient kernels

Authors: Worker 1459 and Worker 1333.

This internal adapter connects the full torus-quotient kernel construction
to finite-Galois domination and conditional descent of represented split
series. It retains every field in the common arbitrary universe `u`, all
characteristics, finite fields and imperfect fields.

`TorusKernelDomination.finiteGaloisKernelDomination` starts with a smooth
affine group `H` over `k`, an actual dominant homomorphism `q : H ⟶ Q` to
a torus, and `HasPointedSplitTorusDomination H`. The full
scheme-theoretic kernel `kernel q` is assumed smooth and connected.
The target torus need not be supplied as split. The existing kernel
extraction theorem derives its splitness and constructs pointed
split-torus domination of the full kernel after a finite separable
extension. The kernel is affine: its inclusion into `H` is closed
because the torus is separated. Finite-Galois refinement of that
parametrization then gives a chosen
`FiniteGaloisSplitTorusDomination (kernel q)`.

This output retains an actual finite Galois field over `k`, a split torus
over that field, a dominant scheme morphism to the direct scalar
extension of the original full kernel, and its identity-section equation.
The parametrization need not be a group homomorphism. No unipotence
assumption is used for this output. It chooses the normal-closure
refinement without retaining a specified embedding of the intermediate
finite separable field.

`RelativeRoot.IsSplitUnipotent.of_finiteSeparable_splitTorusDomination`
is the conditional descent interface for any smooth connected affine
unipotent ground-field group. Its explicit inputs include both
`UnipotentSplitTorusDominationStatement.{u}` and
`RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}`.
It applies to pointed split-torus domination after any given finite
separable extension. Smoothness and affineness persist by pullback;
the existing geometric-connectedness and unipotence base-change
theorems supply the other hypotheses over the extension field.
The supplied domination criterion gives a represented split series
there. The existing finite-separable descent theorem, with the supplied
stable-vector proposition, yields split unipotence of the original
ground-field group.

`TorusKernelDomination.kernel_isSplitUnipotent_of_stableVector`
applies this interface to the field and parametrization chosen by
`finiteGaloisKernelDomination`. It additionally assumes
representation-theoretic unipotence of the actual full kernel and retains
both structural propositions as explicit arguments. A finite Galois field
is finite separable, so the descent interface applies. The conclusion is
literally `RelativeRoot.IsSplitUnipotent (kernel q)`.
`kernelSplitSeriesOfStableVector` chooses a finite length and its actual
`HasSplitSeries` proof on that same full ground-field kernel. No equality
of its length with an extension-field length is asserted.

The provenance is internal composition of the existing full-kernel
diagonalizable extraction, finite-Galois refinement, geometric
connectedness and unipotence under field extension, and conditional
finite-separable split-series descent. Worker 1333 supplied the kernel
extraction and exact domination-criterion target used by this adapter;
Worker 1459 supplied the field-refinement and descent interfaces and
their assembly here. Neither structural proposition is proved by this
module. Existence or smooth connected unipotence of an initial quotient
kernel and the full rational maximal-torus conjugacy theorem remain
separate proof obligations.
