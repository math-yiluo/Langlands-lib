# Isogeny reduction to the nilpotent or semisimple case

Author: Worker 1487.

`Langlands.GroupScheme.SemisimpleIsogenyReductionStatement.{u}` is a
proposition, with no proof supplied here. For every field `k : Type u` and
smooth connected affine group scheme `G` over `Spec k`, it asks for a smooth
connected affine group scheme `G'` over the same field and an actual
finite flat surjective homomorphism `φ : G ⟶ G'`. There are two further
requirements.

First, either `G'` has nilpotent geometric point group, in the published
`IsNilpotentGroupScheme` sense, or its actual algebraic-closure base change
`Gbar` has an element `X : lieKernel Gbar (AlgebraicClosure k)` with
`Lie.IsSemisimpleElement Gbar X` and
`Lie.elementCentralizerLie Gbar X ≠ ⊤`. The kernel here is the actual
dual-number identity kernel. Semisimplicity tests the geometric semisimplicity
of its tangent matrix in every finite dimensional algebraic group
representation. The centralizer is the actual adjoint stabilizer on all
relative tests; its tangent space is a submodule of
`Additive (lieKernel Gbar (AlgebraicClosure k))`. The noncentrality condition
says that this submodule is proper.

Second, every closed torus inclusion `i' : T'.toGrp ⟶ G'` admits a closed
torus inclusion `i : T.toGrp ⟶ G` and a finite flat surjective torus
homomorphism `f : T.toGrp ⟶ T'.toGrp` with `i ≫ φ = f ≫ i'`.
This equality expresses that the scheme-theoretic image of the source torus
is the specified target torus. The statement does not require the torus map
to be surjective on points of every test scheme; finite flat surjectivity
does not imply that stronger condition. Neither torus is assumed maximal
or split.

The provenance is a derived presentation of Milne, *Algebraic Groups*
(2017), Proposition 17.80, printed p.378 (one-based PDF p.394), source ID
`milne-2017-algebraic-groups`. Its conclusion supplies an isogeny with the
nilpotent-or-geometric-semisimple alternative and says that every target
torus is the image of a source torus. For the affine algebraic groups here,
the finite-kernel surjective isogenies of the source are finite flat
surjective morphisms. Restricting such an isogeny to the source torus gives
the finite map `f`; its surjectivity onto the stated target torus makes it
faithfully flat. This yields the displayed actual factorization.

The source's semisimplicity convention, in the paragraph before 17.76 on
printed p.377 (PDF p.393), tests all Lie algebra representations. It
therefore implies the imported predicate that tests differentials of
algebraic group representations. Proposition 17.76 identifies the tangent
space of the actual stabilizer with the bracket centralizer, so its
noncentrality implies the proper-submodule condition used here.
The nilpotence convention and its smooth connected comparison with
classical nilpotence are described in `Nilpotent/Basic.md`, using Milne
16.49. These comparisons are part of the future structural proof, rather
than extra assumptions in this proposition.

Smoothness and affineness imply finite type, and the connected source
has a connected quotient, so the displayed hypotheses and target are
within the source's setting. No perfectness, infinitude, algebraic
closedness, reductivity or characteristic hypothesis is imposed on `k`
or `G`. In particular, the positive-characteristic case in the proof
of 17.80, which iterates infinitesimal isogenies, remains part of the
unproved target. The registered full official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` does not alter 17.80.

This is an input for the infinite-field branch of 17.81. It does not prove
unipotence without tori, reflection of unipotence under an isogeny, or
existence or spanning of rational noncentral semisimple elements. Those
are separate obligations. Its use must remain independent of the parent
no-torus theorem and of maximal-torus preservation deduced from that theorem.
