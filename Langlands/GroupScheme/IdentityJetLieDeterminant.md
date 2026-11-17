# Actual jet determinants and the actual Lie determinant dual

Let `G` be a smooth affine group scheme over an arbitrary scheme `S`.
Supply an affine open cover of `S` and actual cotangent sheaf frames on
that cover with one fixed finite index type `σ`.

The definition `cotangentLieDeterminantDualIso` identifies the existing
actual chosen determinant of `G.cotangentAtIdentity` with the actual
module dual of the existing chosen determinant of `G.Lie`.
The Lie sheaf here is definitionally the internal dual of the actual
cotangent sheaf. The generic actual determinant duality result therefore
applies with the existing cotangent and Lie finite local basis witnesses.

`lieDeterminantPowerIsoOfAffineFrames` composes this comparison with
the actual identity-jet determinant comparison. It gives an actual
module-sheaf isomorphism

`(IdentityJet.determinant G n).obj ≅
  tensorPow
    (finiteLocallyFreeDeterminant
      (G.lie_hasFiniteLocalBasis hG)).dual.obj
    (jetExponent σ n)`.

Both determinant lines and the dual on the right are the existing
actual constructions. The isomorphism includes order zero. It requires
no specified augmentation lifts or compatible truncation splittings.

For `n > 0`, the exponent is positive. The theorem
`lieDeterminantDual_isAmple_of_jet` consequently transfers ampleness
of the actual jet determinant to ampleness of the actual Lie
determinant dual, using reflection of ampleness along an actual
positive tensor-power isomorphism.

The provenance is internal: the comparison combines actual finite-frame
duality with the actual jet determinant-power construction and the
section-generation-locus definition of ampleness. The fixed-index affine
cotangent cover and actual jet determinant ampleness remain explicit
inputs. This unit does not establish jet positivity, remove variable
global rank, account for an ambient stabilizing complement or complete
the parent finite-parabolic ampleness statement.
