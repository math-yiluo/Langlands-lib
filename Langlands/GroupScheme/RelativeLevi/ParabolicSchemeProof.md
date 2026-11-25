# The scheme of parabolic subgroups of a reductive group scheme

`Langlands.GroupScheme.relativeParabolicScheme` proves
`RelativeParabolicSchemeStatement.{u}` for every universe `u`.
For any scheme `S` and reductive group scheme `G` over
`S`, the theorem gives a smooth proper `S`-scheme with a universal relative
parabolic subgroup. For every `S`-scheme and relative parabolic subgroup
of the corresponding pullback of `G`, there is a unique morphism over `S`
for which evaluation of the universal subgroup agrees with the given
subgroup's image functor.

The Lean proof applies
`relativeParabolicSchemeStatement_of_finiteTypes_determinantPositivity_descent`
to three published theorems. [Descent reduction](ParabolicDeterminantDescentReduction.md)

- `relativeParabolicEtaleLocalFiniteTypes`
  supplies an affine étale neighbourhood of each base point and a finite
  family of relative parabolics. Its fibres give one representative of each
  conjugacy class at every field-valued point of the neighbourhood.
  [Finite local types](ParabolicFiniteTypesProof.md)
- `finiteAffineParabolicDeterminantDualAmple`
  gives ampleness of the dual of the Lie determinant of the universal
  conjugate parabolic on the actual finite coproduct of homogeneous quotients.
  [Determinant ampleness](ParabolicDeterminantDualAmpleProof.md)
- `polarizedSmoothProperEtaleDescent`
  gives effective descent for the polarized smooth proper representing
  schemes. Its value universe is `u + 1`, the value universe of the relative
  parabolic presheaf.
  [Polarized étale descent](../../AlgebraicGeometry/Picard/PolarizedSmoothProperDescentProof.md)

The reduction transports ampleness to the restriction of the coherent
determinant dual on that presheaf. Over each affine open of `S`, it uses
compactness to combine finitely many neighbourhoods into an affine étale
surjection and descends the polarized representing scheme along it. Zariski gluing gives the
smooth proper model over `S`. The equivalence with the universal-family
formulation gives the subgroup and the asserted uniqueness.

This formalizes the representability, smoothness and properness clauses of
Conrad's *Reductive group schemes* (2014), Corollary 5.2.9, p. 156
(`conrad-2014-reductive-group-schemes`).
[Source and statement comparison](ParabolicSchemeStatement.md)
