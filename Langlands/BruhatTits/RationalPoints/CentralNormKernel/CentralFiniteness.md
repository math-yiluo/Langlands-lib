# Finiteness of central subgroups with root-of-unity eigenvalues

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement`. The argument is that of the published
`GroupScheme.CentralIntersection.exists_isClosed_isOpen_singleton` (module
`GroupScheme.Derived.CentralIntersection.AlgClosed`, Worker 1408), with its derived-subgroup input
replaced by an explicit eigenvalue hypothesis, and with the closed embedding supplied by the
caller instead of chosen inside the proof.

Let `K` be algebraically closed, `G` a group scheme over `Spec K` with `G.X.left` affine and
`G.X.hom` locally of finite type, `hG : HasTrivialUnipotentRadical G`, `s : S ⟶ G` a closed
subgroup with `IsCentral s`, and `ρ : MatrixRepresentation G N` a closed immersion. Assume
`heig`: for every rational point `y` of `S`, every root of the characteristic polynomial of
`ρ.rationalMatrix (y ≫ s)` is an `m`-th root of unity, `m ≠ 0`.

- `exists_isClosed_isOpen_singleton_of_eigenvalues`: some point of `S.X.left` is closed and
  open. Proof. Let `f : H ⟶ S` be the identity component of the reduced subgroup
  (`ReducedSubgroup.exists_reducedIdentityComponent`): `H` is smooth, connected, and `f` has open
  image. `f ≫ s` is central, so its range is normal and the rational points of `H` commute. `H`
  is reduced and affine; the restriction of `ρ` to `H` is a closed immersion and, by `heig`, all
  eigenvalues of rational points of `H` are `m`-th roots of unity. `isUnipotent_of_eigenvalues`
  makes `H` unipotent, and `hG` makes it trivial. So the image of `f` is the identity point of
  `S`, which is closed (`pointEquivClosedPoint`) and open.
- `finite_rationalPoints_of_eigenvalues`: `S` has finitely many rational points. `S.X.left` is
  finite by `finite_of_isOpen_singleton` (module `AlgClosed`), and rational points correspond to
  closed points (`rationalPointEquivClosedPoint`).
