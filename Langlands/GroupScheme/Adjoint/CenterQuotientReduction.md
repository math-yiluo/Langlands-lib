# Reduction of the centre-quotient theorem to algebraically closed fields

This module reduces `CenterQuotientReductiveStatement` (module
`Langlands.GroupScheme.Adjoint.CenterQuotientStatement`) to a statement over an algebraically
closed field that concerns only the unipotent radical.

## `CenterQuotientGeometricCoreStatement`

This is an internal intermediate proposition, derived from the target statement. It is not a
literature statement and it is not assumed anywhere as a premise of a published theorem. For every
universe `u`, every algebraically closed field `K : Type u`, every pair of group schemes `G`, `Q`
over `Spec K` and every homomorphism `q : G ⟶ Q`, it requires that the following hypotheses give
`HasTrivialUnipotentRadical Q`:

- `G.X.hom` is smooth and affine, and `G.X.left` is connected;
- `G` has trivial unipotent radical (`HasTrivialUnipotentRadical G`);
- `Q.X.hom` is affine and locally of finite type;
- `RelativeRoot.IsFppfQuotient (center G) q` holds: `q` is flat, surjective and locally of finite
  presentation, and the range of its actual kernel inclusion is the full scheme-theoretic centre
  of `G` on every test scheme.

Over an algebraically closed field these are the hypotheses of the target for the base change of
`G` and `q`, with the conclusion restricted to the one hard field of `IsConnectedReductive Q`.

## `RelativeRoot.IsFppfQuotient.baseChange_center`

If `q` is an fppf quotient by the full centre `center G` over a base `S`, then for every
`b : S' ⟶ S` the base-changed homomorphism is an fppf quotient by the full centre
`center (G_{S'})`. Proof: rewrite with `center_baseChange` (the centre functor commutes with base
change) and apply `RelativeRoot.IsFppfQuotient.baseChange`.

## `centerQuotientReductive_of_geometricCore`

The core statement implies `CenterQuotientReductiveStatement.{u}`. Given `k`, `G`, `Q`, `q` with
`IsConnectedReductive G`, `Q` affine and locally of finite type, and the fppf quotient property by
`center G`, the proof supplies the four fields of `IsConnectedReductive Q`:

- smoothness of `Q.X.hom` from `RelativeRoot.IsFppfQuotient.smooth_target` (an fppf quotient of
  a smooth group over a field is smooth);
- affineness of `Q.X.hom` from the hypothesis;
- connectedness of `Q.X.left` from `RelativeRoot.IsFppfQuotient.connectedSpace` (a surjective
  image of the connected space `G.X.left`);
- the trivial unipotent radical of `Q` after base change along `toAlgebraicClosure k`, by applying
  the core statement to `K = AlgebraicClosure k` and the base changes of `G`, `Q` and `q`.

The hypotheses of the core over `AlgebraicClosure k` hold as follows. Base change preserves
smoothness and affineness of `G` and affineness and local finite type of `Q`, since the structure
maps are pullbacks. Connectedness of the base change of `G` is
`IsConnectedReductive.connectedSpace_toAlgebraicClosure`. The trivial unipotent radical is the
`hasTrivialGeometricUnipotentRadical` field of `IsConnectedReductive G`. The quotient property is
`baseChange_center` above.
