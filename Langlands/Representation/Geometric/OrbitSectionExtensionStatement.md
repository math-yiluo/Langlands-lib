# Compact section extension from a locally closed coset orbit

`ClosedOrbitSectionExtension` is a proposition definition, not a proof or
an assumed extension operator. It asserts a concrete pointwise extension
property needed for the closed-subgroup Mackey support filtration.

For a locally compact Hausdorff nonarchimedean sigma-compact group `G`, closed
subgroups `P,Q`, and `w : G`, let `Z` be the actual orbit of `P w^-1` in
`P \ G`. If `U` is open, contains all of `Z`, and `Z` is closed in the subspace
`U`, every compactly induced function on
`(Q intersect w P w^-1) \ Q`, with covariance obtained from a smooth complex
representation of `P` by conjugation by `w^-1`, extends to an actual compactly
induced function on `G`. The extension has projected nonzero support inside
`U` and agrees pointwise with the input under `q -> w^-1 q`.

All compactness, covariance and uniform open right stabilizer conditions come
from the existing `Induction.CompactFunctions` type. The statement quantifies
over every smooth representation in the independent carrier universe `uV`,
with no finite-dimensionality, admissibility or finite-length assumptions.
It does not give the caller a local section, an orbit homeomorphism,
surjectivity or an isomorphism as an input. No natural choice of extension is
asserted: naturality of the eventual Mackey comparison comes from restriction,
which is canonical, and passage to the kernel quotient.

The open set need not itself be invariant. In the intended application it is
the next open initial union in `OrderedDoubleCosets`, and its relatively closed
orbit is the difference from the preceding open initial union. Thus the output
belongs to the actual upper support step; the pointwise extension property
will prove surjectivity of the actual restriction map.

## Provenance and proof boundary

This is a derived direct-section formulation of the extension mechanism in
Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), sections 5.3–5.15, printed pages 461–465 (PDF pages 22–26). These pages
were read. Section 5.11 gives exactness of compactly supported restriction
across a closed complement. Sections 5.14–5.15 identify the orbit sheaf with
induction from its stabilizer, and case III has `U=V={1}` in the source's group
notation. The open subset called `U` in this Lean statement is a subset of
`P \ G`, not the source's localization subgroup.

The planned proof may construct and glue finitely many locally constant
covariant patches instead of introducing sheaves. This pair does not claim
that construction is implemented or that the source gives this exact Lean
formulation. The section-extension proof is a separate obligation, as are
orbit topology, compactness of restriction, identification of its kernel, and
the natural graded quotient isomorphism. The latter results must use proved
prerequisites and leave the published Mackey target and its imports unchanged.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Retained original SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Author: Worker 112.
