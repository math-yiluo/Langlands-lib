# Explicit jet Grassmannian embeddings of actual quotients

Let a group functor over an arbitrary affine base be corepresented by `B`.
Let `K` contain the `(n+1)`-st power of the actual augmentation ideal.
Suppose the ambient jet module `B/I^(n+1)` is finite and the quotient
`B/K` is finite projective. Let `q : G → Q` be an actual fpqc quotient
with proper `Q` over the base. Its exact all-test fiber condition is
that two group points have the same image if and only if their quotient
stabilizes the subscheme cut out by `K`.

`QuotientJetEmbeddingData` retains a finite projective complement `C` making
`(B/K) × C` free of constant rank, the represented Grassmannian of quotients
of `(B/I^(n+1)) × C` of that rank, and an actual closed embedding from the
supplied `Q` to that Grassmannian. Its `fac` field identifies composition
with the original quotient projection with the explicit stabilized jet
orbit map. Thus the affine charts and classification equivalences remain
available for comparison with actual jet module sheaves.

`quotientJetEmbeddingData` constructs these data. Finite projectivity supplies
the complement. The published orbit-map kernel calculation and the supplied
fiber condition identify the fibers of the orbit map with those of `q`.
Fpqc effective descent gives the map out of the actual `Q`; equality of
all-test fibers makes it a monomorphism. The Grassmannian is proper since
its input module is finite. Properness of `Q` and separatedness of the
Grassmannian then make the embedding proper; a proper monomorphism of
schemes is a closed immersion.

This internal construction refines the existing orbit-map and homogeneous
quotient descent results by retaining their concrete Grassmannian data. It
asserts no existence of the required stabilizing jet or actual quotient and
no determinant positivity. Those are separate geometric inputs and conclusions.
