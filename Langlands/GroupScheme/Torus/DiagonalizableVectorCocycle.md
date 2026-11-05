# Contraction of regular vector two-cocycles on diagonalizable groups

Worker 1552. This is an internal construction over a field k in an arbitrary universe u. The character group Λ is any abelian group, and D = D(Λ) is the actual diagonalizable group scheme. The coefficient group V is supplied with an automorphic action a of D and vector coordinates e on every test scheme, satisfying `IsLinearVectorCoordinates a e`. The section declares V affine; no finite-generation, torsion-free, characteristic-zero or reducedness assumption is used. No scheme section or extension group is an input.

The two-cochain is an actual regular morphism `cochain : D.X ⊗ D.X ⟶ V.X`. Its evaluation `value` is composition with the pair of test points. Assuming the identity

`value t r * value (t * r) w = a.act t (value r w) * value t (r * w)`

on every test scheme, `averageHom_coboundary` and `exists_coboundary` supply an actual regular morphism b : D.X → V.X with

`value t r * ((t * r) ≫ b) = a.act t (r ≫ b) * (t ≫ b)`

on every test scheme. These identities use multiplication in V's test-point group, which the given coordinates identify with addition of vectors.

The implemented proof takes the zero coefficient of `cochain(t, universal point)` in the group algebra A[Λ], coordinate by coordinate, to define `averageVector`. The coordinate equivalence gives `averagePoint`. The translation and coefficient lemmas in `Diagonalizable.Averaging` prove invariance under translation of the averaging variable. Naturality and linearity of the action identify the zero coefficient of the acted-on cochain with the action on its average. Applying this coefficient map to the cocycle identity proves `cocycle_add_averageVector` and then `averagePoint_coboundary` on affine points.

Coefficient-extension naturality proves that these averages form a natural family. The existing affine Yoneda helpers from `Rational.SplitTorusVectorExtension` construct `averageHom` and its evaluation identity. Affineness of D × D gives the universal coboundary equation, and precomposition with the pair of arbitrary test points gives the all-test equation. The construction of b and its naturality do not depend on the cocycle hypothesis; that hypothesis is used only for the coboundary identities.

This generalizes the coefficient calculation in `DiagonalizableVectorExtension` from section defects to arbitrary regular two-cocycles. It is a helper for the unrestricted additive extension splitting theorem and does not itself assert the existence of a section of an extension. All provenance is internal, through the imported constructions and the proof described above.
