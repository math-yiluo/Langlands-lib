# Detection of functions and factorizations by rational points

This helper module serves the proof of
`Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`
(task 6b07dcd2-af39-4c69-8ade-d0faa997a49f). It shows that a morphism into an
affine scheme factors through a closed subscheme when it does so at every
rational point, provided rational points detect global functions on the source.
It also gives the usual sufficient condition for detection: the source is
reduced (for example smooth) and its rational points are dense. These are
standard facts. The arguments were written for this formalization and follow
the Library's `IsSplitTorus.exists_factor_of_kpoints`
(`Langlands.GroupScheme.Rational.SplitTorusRationalDetection`).

The detection predicate is the Library's
`Langlands.GroupScheme.RationalPointsDetectFunctions X`: a global section of X
that vanishes at every rational point Spec k ⟶ X is zero. Density is the
Library's `Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPoints`.

Everything is in the namespace `Langlands.GroupScheme.RationalDensity`. Fix a
field k and write S = Spec k. All objects are objects of `Over S`.

## Factoring through closed immersions

- `exists_factor_of_ker_le`: let j : Y ⟶ Z be a morphism over S whose
  underlying morphism is a closed immersion, with Z affine, and let f : X ⟶ Z.
  If the kernel of j on global sections is contained in the kernel of f on
  global sections, then f = l ≫ j for some l : X ⟶ Y over S. The ideal sheaves
  of j and f are the sheaves of these kernels (`Scheme.ker_of_isAffine`), so
  the ideal sheaf of j is contained in that of f, and Mathlib's
  `IsClosedImmersion.lift` gives the factorization of schemes. It lies over S
  because j does.

## Detection by rational points

- `rationalPointsDetectFunctions_of_dense`: if X is reduced and has dense
  rational points, then rational points detect functions on X. Let s be a
  global section vanishing at every rational point. If its basic open set were
  nonempty, it would contain the image of some rational point x. The preimage
  of that basic open set under x is the basic open set of the image of s, which
  is zero, so it is empty. Hence the basic open set of s is empty, and on a
  reduced scheme this forces s = 0.
- `RationalPointsDetectFunctions.exists_factor`: let rational points detect
  functions on X, and let j : Y ⟶ Z and f : X ⟶ Z be as in
  `exists_factor_of_ker_le`. Suppose that for every rational point x of X,
  x ≫ f = y ≫ j for some rational point y of Y. Then f factors through j. A
  section s of Z killed by j is killed by y ≫ j, hence by x ≫ f, for every x.
  So the image of s in Γ(X) vanishes at all rational points and is zero, and
  `exists_factor_of_ker_le` applies.
- `hasDenseRationalPoints_tensorUnit`: the unit object 𝟙_ = S has dense
  rational points, since its identity is a rational point and is surjective.
- `rationalPointsDetectFunctions_of_smooth`: if X is smooth over S and has
  dense rational points, rational points detect functions on X. A scheme smooth
  over a field is reduced (the Library's
  `SmoothReducedProof.isReduced_of_smooth_over_field`).
