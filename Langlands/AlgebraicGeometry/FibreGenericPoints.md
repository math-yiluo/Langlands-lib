# Generic points of all scheme fibres

This internal construction packages the finite-point step used after
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4 (printed p.155),
for a DVR base. It uses Mathlib's actual scheme-theoretic fibres and their
embeddings into the total scheme. It has no group-scheme assumptions.

For any morphism `p : X ⟶ S` between schemes in universe `u`,
`fibreGenericPoints p` is the union, over all points `s : S`, of the images
of the generic points of the irreducible components of `p.fiber s`.
`FibreGenerizationDense p U` means that every point `x : X` has a
generization `y` in `U` with `p y = p x`.

`exists_fibreGenericPoint_specializes` places `p.asFiber x` in an
irreducible component of its fibre and chooses that component's generic
point. Mapping its specialization to `X` gives the required same-fibre
generization.

`fibreGenericPoints_subset_iff` proves that a subset of `X` contains all
these fibre generic points if and only if it is fibre-generization dense.
For the reverse implication, the fibre embedding reflects specialization,
and a component generic point has no proper generization in the fibre.
This equivalence does not require the subset to be open, finite-type
hypotheses, or nonempty fibres.

`finite_fibreGenericPoints` assumes the type of base points is finite and
`p` is quasi-compact and locally of finite type. Every fibre is then
noetherian and has finitely many component generic points; taking their
images and the finite union proves finiteness.

These declarations implement a derived topological part of the source's
argument. They do not assert that these points have a common affine
neighbourhood; that is a separate geometric obligation.
