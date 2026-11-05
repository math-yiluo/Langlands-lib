# Represented split series for solvable groups over algebraically closed fields

Authors: Worker 1472 and Worker 1448.

`Langlands.GroupScheme.algebraicallyClosedSplitSolvable` proves exactly
`AlgebraicallyClosedSplitSolvableStatement.{u}`. For every algebraically
closed field `k : Type u` and every smooth affine group scheme `G` over
`Spec k`, connectedness and the existing geometric-point predicate
`IsSolvableGroupScheme G` imply the full existing
`IsSplitSolvableGroupScheme G`. There is no characteristic or dimension
restriction, and the trivial group is included.

The implemented proof first applies
`solvableTorusQuotient_of_kernel_prerequisites` with the published proofs
`triangularDiagonalKernelGeometry` and `unipotentClosedSubgroup`.
The quotient construction uses a closed Lie–Kolchin embedding, factors
the diagonal map through its actual split-torus image, and takes the
scheme-theoretic diagonal kernel. The two supplied proofs establish
smoothness and connectedness of that kernel, and its unipotence by its
closed inclusion into the unitriangular group. The result gives actual
group schemes `N` and `Q`, a closed inclusion `i : N ⟶ G`, and an fppf
quotient `q : G ⟶ Q`. Its kernel subgroup functor is the range of `i`
on every relative scheme test, `N` is smooth connected and unipotent,
and `Q` is a split torus. These are conclusions of the imported proofs,
with no additional structural hypothesis on `G`.

The closed inclusion into affine `G` makes `N` affine: its structure map
is the composite of the closed immersion with the affine structure map
of `G`. The published theorem `Unipotent.algebraicallyClosedSplit`
therefore supplies the full represented split-unipotent series on `N`.
That theorem uses closed-subgroup unipotence, proper smooth
closed-subgroup induction, actual quotients by reduced identity cores,
and the one-dimensional unipotent classification.

Finally,
`IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient`
combines this series with the represented split-torus series on `Q`.
Its extension construction pulls the quotient series back along `q`
and joins it to the kernel series. The smooth connected affine kernel
supplies smoothness and geometric connectedness of the quotient map.
The resulting finite series uses actual smooth connected closed normal
subgroups and represented fppf quotients with the existing natural
one-dimensional vector-group or Gm identifications. Its terminal group
is trivial on every relative scheme test, including nonreduced tests.
The extension theorem also retains the original smoothness, affineness,
connectedness and geometric-point solvability fields of the conclusion.

The provenance of this module is internal composition of the cited
published Library theorems. All structural inputs are supplied by those
proofs.
The original correspondence with Milne's Proposition 16.34 is documented
in the unchanged target statement pair; this proof uses the
unipotent-kernel and split-torus extension route implemented in the
imported modules. It uses no Borel-conjugacy theorem.
