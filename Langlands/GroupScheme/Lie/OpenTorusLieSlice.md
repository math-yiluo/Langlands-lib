# An open set in the regular torus Lie slice over a complete field

In `OpenTorusLieSliceStatement`, let a torus map to a smooth affine group scheme with finite Lie coordinates
over a complete nontrivially normed field. Write `B` for a basis matrix of
the torus Lie centralizer. There is a left inverse `D` of `B` and a nonempty
open set in the coordinate space such that every vector in the open set
is an adjoint translate of a vector `B *ᵥ t`. On that set the sum of the
vector's bracket matrix and the projection `B * D` is invertible.

Use a regular slice parameter over the ground field. Invertibility at that
parameter gives surjectivity of the tangent map at the corresponding point
of the slice. Restrict the source to the smooth locus and use openness on
complete-field points. Polynomial evaluation gives a continuous map from
coordinate vectors to the actual affine-space points. Pull back the image
of the smooth locus along that map and intersect with the nonvanishing set
of the determinant. The initial regular parameter belongs to the resulting
open set.

This is the Lie-slice form of the local openness step used for approximation
of maximal tori. See Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), Theorem 2.18, printed pp. 104–105, and Proposition 7.3,
Corollary 3, printed p. 405.
