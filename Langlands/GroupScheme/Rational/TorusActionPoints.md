# The torus action on points over arbitrary test schemes

Let `b : AutomorphicAction (splitTorus (Spec R) I) (groupScheme F e)` be an action of a
split torus on a corepresented affine group scheme, and let
`TorusAction.ofAutomorphicAction e b` be the induced action on algebra points (Worker 1239's
`Rational.TorusActionBridge`). This module shows that, on every test scheme `T`, `b` acts
through the unit coordinates `splitTorus.pointsEquiv I T s` of the torus point `s`. All
declarations are in namespace `Langlands.GroupScheme.Corepresented`.

## Statements

- `unit_appTop_ΓSpecIso_inv`: pulling back along the unit
  `T ⟶ Spec Γ(T)` of the adjunction `algΓAlgSpecAdjunction R` sends
  `(Scheme.ΓSpecIso Γ(T)).inv a` back to `a`, for every global function `a` of `T`.
- `algebraPointsEquiv_affinizationFactor`: let `s` be a point of the split torus over `T`,
  and `Lie.affinizationFactor _ s` its factorization through `Spec Γ(T)`. The unit
  coordinates `splitTorus.algebraPointsEquiv` of this factor are the unit coordinates
  `splitTorus.pointsEquiv I T s` of `s`.
- `pointsEquiv_act`: for every test scheme `T`, torus point `s` and point `x` of
  `groupScheme F e`,
  `pointsEquiv F e T (b.act s x) =
    (TorusAction.ofAutomorphicAction e b).act (splitTorus.pointsEquiv I T s) (pointsEquiv F e T x)`.

## Proofs

`unit_appTop_ΓSpecIso_inv` combines two facts. The Library's
`Corepresented.adjunction_homEquiv_symm_apply` describes the adjoint of a point by pulling back
global functions. The adjoint of the unit is the identity, by the left triangle identity
`left_triangle_components`.

For `algebraPointsEquiv_affinizationFactor`, write `s` as the unit followed by its factor
(`Lie.unit_affinizationFactor`). By `splitTorus.pointsEquiv_naturality`, the unit
coordinates of `s` are the pullbacks along the unit of those of the factor. These agree with
the affine identification of the factor (`Gm.affinePointsEquiv`, through `ΓSpecIso`), by the
first lemma.

`pointsEquiv_act` follows the proof of the bridge's `exists_pointsEquiv_act`. It factors `s`
and `x` through `Spec Γ(T)` (`Lie.unit_affinizationFactor`, `unit_comp_affineFactor`) and uses
naturality of the action, `pointsEquiv_unit_comp` and `affinePointsEquiv_act`. It then
identifies the coordinates by `algebraPointsEquiv_affinizationFactor`.

## Provenance

Internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task 023326af). It
sharpens the bridge's existence statement `exists_pointsEquiv_act` to an explicit coordinate
formula. The intertwining of the vector-group action of weight `r • a` with the lifted
action (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8) needs this
formula on all test schemes.
