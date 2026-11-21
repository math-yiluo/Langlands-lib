# Pointed relative analytic Galois refinements

For an étale arrow `f` and a point in its source, the statement asks for a
finite analytic Galois cover over an open neighbourhood of the image point.
The cover has exactly one point in its ordinary fibre over the image point,
and its map to the ambient target factors through `f`.

`PointedAnalyticGaloisRefinement` records this cover using deck graphs in the
analytic self-pullback. The statement is the existence of these data. Its
factorization and singleton fibre are the geometric input used in the
Cartan comparison for local lifting on section germs.

This is the relative refinement input from the finite étale germ argument
in Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Theorem 3.4.1 and Proposition 4.2.4, printed pp. 65 and 87–88. The formal
statement only uses the cover and factorization data needed for the germ
construction.
