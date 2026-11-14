# Vector weights of a numbered simply connected split orthogonal cover

`Langlands.GroupScheme.OrthogonalMatrix.NumberedCoverVectorStatement` is an
unproved proposition at every universe `u`. It is the split orthogonal
representation prerequisite for `SpinCoverVectorWeightsStatement`.

Let `k` be any field, `n ≥ 4`, and `G` an affine group scheme over `k` with
an actual split pinning `p`. Suppose `G` is simply connected and
`pi : G → O_(2n)^0` is a central isogeny to the identity component of the
published hyperbolic orthogonal group `OrthogonalMatrix.groupScheme (Fin n)`.
Let `e` number the simple-root support of `p` by `Fin n`, with Cartan matrix
exactly `CartanMatrix.D n` in that numbering.

The alignment hypothesis concerns the supplied cover and the supplied torus.
For each simple vertex numbered zero, every character with pairing one
against its coroot and zero against all other simple coroots must kill the
kernel of `p.inclusion ≫ pi`. Killing the kernel means that it sends every
kernel point over every relative test scheme to the identity of `Gm`.
This has the same scheme-valued meaning as the published
`TitsIndexData.FundamentalWeightTrivialOnKernel`, with a split pinning
already over `k`. It does not replace that condition by a condition on
field-valued points. Including the identity component into the full
orthogonal group does not change the kernel.

The conclusion supplies characters `eps i` of the actual torus `p.torus`
and a basis `b` of the natural `2n`-dimensional row module. They satisfy:

- A simple vertex numbered `i` with `i + 1 < n` has root
  `eps i - eps (i + 1)`. The vertex numbered `n - 1` has root
  `eps (n - 2) + eps (n - 1)`.
- Every signed pair `s eps i + t eps j` with `i ≠ j` and `s,t ∈ ℤˣ`
  is a root of the supplied root datum.
- The basis is indexed by `Fin n × ℤˣ`. For every commutative coefficient
  `k`-algebra `R`, every actual `R`-point `t` of the torus, and every
  index `(i,s)`, the coefficient extension of `b (i,s)` is an eigenvector
  of right multiplication by the inverse matrix of `pi(t)`, with
  eigenvalue the character `s eps i` evaluated at `t`.

The matrix comes from the composite of the actual cover, the identity
component inclusion, and the published orthogonal matrix inclusion into
`GL_(2n)`. Scalar extension of the basis vectors is coordinatewise
`algebraMap k R`; no separate basis choices are made over coefficient
algebras. A basis indexed by all signed coordinates records multiplicity
one even if some restricted weights later coincide along a cocharacter.
The inverse is taken in `GL`, before coercion to a matrix.

The pinning supplies a split maximal torus and an actual finite reduced
root datum. No algebraic closedness, infinitude, perfectness or
characteristic restriction is imposed on `k`. In particular,
characteristic two is included; the kernel condition retains its
nonreduced scheme information there. The proposition does not concern
only the standard diagonal torus, and assumes no chosen conjugation of
the supplied torus to it.

## Source and derived formulation

The source is Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*
(1998), source ID `knus-merkurjev-rost-tignol-1998-book-of-involutions`.
In the registered copy, PDF page number is printed page number plus 23.

Section 24.A, printed p. 355 (PDF p. 378), lists the type-`D_n` roots
`±e_i ± e_j`, the simple roots
`e_1-e_2, …, e_(n-1)-e_n, e_(n-1)+e_n`, the weight lattice, and its
three nonzero minimal dominant weights: the vector weight `e_1` and the
two half-spin weights. It also records the group `S_3` of diagram
symmetries in rank four, in contrast to the order-two symmetry in higher
rank. The Lean numbering is the source numbering decreased by one.

Section 25.A, printed p. 359 (PDF p. 382), realizes the split orthogonal
group on a hyperbolic quadratic space and its split diagonal maximal
torus as `diag(t_1, …, t_n, t_1^-1, …, t_n^-1)`. It computes the roots
and identifies the corresponding simply connected group as the spin
group. The natural row representation and its inverse-right convention
therefore have the same signed coordinate characters, with the signs
interchanged on the two halves.

Section 27.B, printed p. 379 (PDF p. 402), identifies the vector
representation with highest weight `e_1` and the two half-spin highest
weights. The vector character factors through the connected orthogonal
group. That paragraph excludes `n = 4`; the exceptional case is addressed
on printed p. 563 (PDF p. 586), where the degree-eight algebra with
orthogonal involution is referred back to the Section 27.B description.
Together with the rank-four weight lattice in Section 24.A, this explains
why the actual cover kernel distinguishes the vector end vertex among
the three end vertices. In characteristic two that distinction uses the
scheme kernel, not its field-valued points.

The retained author errata and separately labelled unofficial page-sorted
comments (source `book-involutions-author-errata-2026-11-13`) were read.
The page-379 comment changes the central-character notation `C*` to
`C*_sep`; it does not change the weight formulas. No listed correction
changes the cited passages on pp. 355, 359 or 563.

This precise statement on an arbitrary supplied split pinning, an actual
central cover, its scheme-valued kernel alignment, and a single basis
satisfying the equation over all coefficient algebras is a derived
formulation. It is not a separately printed assertion of the source.
Its intended derivation transports the split diagonal vector weights
through the actual torus and root-datum comparisons. The alignment fixes
the vector end vertex in rank four; the remaining fork interchange can
be implemented by changing the sign of the last vector character.
The natural representation's one-dimensional weight spaces give the
basis, and the character equations extend to all coefficient algebras.
All of these transport, normalization and representation assertions
remain proof obligations of the proposition.

This prerequisite supplies no Morita comparison for division algebras,
no descent of characters from an algebraically closed extension, and no
formula for the division-algebra dimensions of cocharacter weight spaces.
Those comparisons are still needed for the host statement.
