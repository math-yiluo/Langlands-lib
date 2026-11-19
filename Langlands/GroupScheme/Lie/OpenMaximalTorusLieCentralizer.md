# An open set with prescribed connected Lie centralizers

In `OpenMaximalTorusLieCentralizerStatement`, let `s : S.toGrp ⟶ H` be a
maximal torus of an affine connected reductive
algebraic group over a complete nontrivially normed field of characteristic
zero, with finite Lie coordinates. There is a nonempty open set of
coordinate vectors whose represented connected centralizer is a conjugate
of `S`. The comparison is an isomorphism over the field, compatible with
the embeddings into `H` after conjugation by an actual point of `H`.
The result uses an affine smooth closed representative of the centralizer.

On the open torus Lie slice, a vector is the adjoint image of a vector in
the Lie algebra of `S`. Thus a conjugate of `S` factors through the
centralizer and through its identity component. If `B` is the Lie
centralizer basis matrix and `D` its left inverse, then `D` is injective
on the Lie algebra of the vector centralizer. Indeed the bracket matrix
vanishes there and its sum with `B * D` is invertible. The centralizer's
Lie dimension is therefore at most that of `S`. The inclusion of the
conjugated torus gives the reverse bound and is an isomorphism by the
smooth connected equal-dimension criterion.

The argument implements the local openness of the prescribed conjugacy
class in the maximal-torus approximation of Platonov and Rapinchuk,
*Algebraic Groups and Number Theory* (1994), Theorem 2.18, printed
pp. 104–105, and Proposition 7.3, Corollary 3, printed p. 405.
