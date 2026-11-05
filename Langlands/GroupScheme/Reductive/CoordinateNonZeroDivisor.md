# Coordinates equal to one at the identity are non-zero-divisors

Worker 1628 derives this internal result from two Library theorems: a smooth
connected scheme over a field is integral, and an integral affine group has a
domain as its Hopf coordinate algebra. The file supplies the non-zero-divisor
condition, condition 4, of `SteinbergBigCellStatement` from its normalization
condition, condition 3, `d(1) = 1`. The hypothesis forms match those of that
statement, so the conclusion can be used there directly. No Borel subgroup,
torus or big cell is involved.

## Setting

Let `k` be a field and `G` a group scheme over `Spec k` with affine structure
morphism. `AffineCoordinates.algebra G` is its coordinate algebra, and
`pointAlgebraHom G T g` evaluates coordinates at a point `g` with values in a
test scheme `T`. The identity test scheme is `Over.mk (𝟙 (Spec k))`, and `1`
is the identity rational point of `G`.

## Declarations

- `nontrivial_algΓ_identityTest`: the global sections of the identity test
  scheme form a nontrivial ring. These sections are `Γ(Spec k, ⊤)`, which
  Mathlib's `Scheme.ΓSpecIso` identifies with the field `k`.
- `identityEvaluation G` is the evaluation of coordinates at the identity
  rational point, `pointAlgebraHom G (Over.mk (𝟙 (Spec k))) 1`.
  `identityEvaluation_apply` unfolds it. `identityEvaluation_eq` states that it
  is the coordinate counit followed by the structure map of `k` into the global
  sections; this is the Library's `pointAlgebraHom_one`.
- `isDomain_of_isConnectedReductive`: if `G` is connected reductive
  (`IsConnectedReductive`), its coordinate algebra is a domain. A connected
  reductive group is smooth and has connected underlying space. Smoothness
  gives local finite type, hence a locally noetherian scheme. The Library's
  `CharacterLatticeProof.isIntegral_of_smooth` then makes the underlying
  scheme integral. The Library's `AutomorphicAction.coordinate_isDomain` turns
  this into the domain property of the coordinate Hopf algebra, whose
  underlying ring is the coordinate algebra.
- `ne_zero_of_pointAlgebraHom_one`: a coordinate `d` with
  `pointAlgebraHom G (Over.mk (𝟙 (Spec k))) 1 d = 1` is nonzero. Otherwise
  `0 = 1` in the nontrivial global sections.
- `mem_nonZeroDivisors_of_pointAlgebraHom_one`: on a connected reductive
  group, such a `d` lies in `nonZeroDivisors (algebra G)`. A nonzero element of
  a domain is a non-zero-divisor (Mathlib's `mem_nonZeroDivisors_of_ne_zero`).
- `mem_nonZeroDivisors_of_isSimplyConnected`: the same conclusion for a simply
  connected `G` (`IsSimplyConnected`). Simple connectedness includes
  semisimplicity, which includes being connected reductive.

## Scope

The file does not construct any coordinate `d`. It shows only that condition 4
of `SteinbergBigCellStatement` follows from condition 3 for every coordinate of
a simply connected group, so whoever proves that statement need not check
condition 4 separately.
