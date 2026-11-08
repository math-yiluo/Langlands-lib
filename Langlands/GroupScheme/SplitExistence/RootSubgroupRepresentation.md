# Root maps of a Chevalley group represent the intrinsic root subgroups

This internal unit connects the Chevalley groups of the split existence
construction (`ChevalleyData.ChevGroup`, module
`Langlands.GroupScheme.SplitExistence.Centralizer`) with the Library's
intrinsic root subgroups `RelativeRoot.subgroup`. For Chevalley data `D` of a
reduced root datum `P` with finite index type and finite free character
lattice, and a Chevalley group `G` over a field `k`, each root homomorphism
`G.u j : 𝔾ₐ → G.H` represents the entire intrinsic root subgroup of the
character `charOf k (P.root j)` of the torus `G.t`, on every test scheme.
The universe and the characteristic are arbitrary.

## Root exponentials over a ring

Let `K` be a commutative ring.

- `x_apply_of_e_one_ne_zero` states that if the integral matrix `D.e j 1` has a
  nonzero entry at `(c, d)`, then the `(c, d)` entry of the root exponential
  `D.x j s` is `s` times that entry. In the truncated exponential
  `Σ_k s^k e_j(k)`, a nonzero entry of `e_j(k)` at `(c, d)` forces
  `wt c = wt d + k • root j` (field `e_weight`). Since the weight lattice is
  torsion-free and the root is nonzero, only `k = 1` contributes.
- `one_mem_span_e_one` states that the entries of `D.e j 1` generate the unit
  ideal of `ℤ`. Otherwise a prime divides the generator of that ideal, and
  hence every entry, contradicting the field `e_one_map_ne_zero`.
- `x_injective` states that `s ↦ D.x j s` is injective. If `x_j(s) = x_j(s')`,
  then `x_j(s - s') = 1`. The entries above give `(s - s') m = 0` for every
  entry `m` of `e_j(1)`, because these entries lie off the diagonal. The unit
  ideal property then gives `s = s'`.

## Scheme statements

- `mono_rootToGL`: the root homomorphism `D.rootToGL k j` into the linear group
  is a monomorphism, by `x_injective` on the points of every test scheme.
- `gaCoord_scalarPoint` and `charValue_charOf` identify the coordinate of a
  scalar point of `𝔾ₐ`, and the value `VectorGroup.charValue` of the character
  `charOf k ξ` at a torus point, with the expressions used by the point
  formulas of the construction.
- `ChevGroup.mono_u`: each `G.u j` is a monomorphism, because its composite
  with the closed embedding `G.i` is `D.rootToGL k j`.
- `ChevGroup.u_isTorusEquivariant`: `G.u j` satisfies the published predicate
  `VectorGroup.IsTorusEquivariant G.t (G.u j) (charOf k (P.root j))`. On every
  test scheme, conjugation by a torus point multiplies the parameter by the
  root character. The proof cancels the monomorphism `G.i`, compares matrices
  in `GL_n` of the global sections, and applies the published
  `torusHom_conj_x`.
- `ChevGroup.hasNoHigherRoots_charOf`: no multiple `n • charOf k (P.root j)`
  with `n ≥ 2` is a root of `G.t`. By the published `roots_t`, such a root
  would be `charOf k (P.root j')`, so `P.root j' = n • P.root j`. Reducedness
  of `P` then forces `n • P.root j = ± P.root j`, which is impossible for
  `n ≥ 2` in a torsion-free lattice.
- `ChevGroup.represents_root`: `(RelativeRoot.subgroup G.t (charOf k (P.root j))).IsRepresentedBy (G.u j)`.
  It applies the published `VectorGroup.IsTorusEquivariant.represents_root`.
  Its inputs are connected reductivity (`ChevGroup.isConnectedReductive`), the
  split torus `isSplitTorus_Tk`, maximality (`ChevGroup.isMaximalTorus`), the
  root property from `roots_t`, and the previous lemma. This theorem assumes
  that `G.H` is affine and locally of finite type over `k`, as `roots_t` does.

## Rational coordinates

- `gaRationalEquiv k : Multiplicative k ≃* (Spec k → 𝔾ₐ)` identifies the rational
  points of `𝔾ₐ` with the field. It composes the inverse of the published
  `Scheme.ΓSpecIso`, the one-coordinate identification, and the inverse of the
  published standard coordinates. `gaCoord_gaRationalEquiv` states that the
  coordinate of the point attached to `s` is the global function corresponding
  to `s`.
- `ChevGroup.rootPointsEquiv j` is the published point equivalence of the
  representation `represents_root`, from rational points of `𝔾ₐ` to the
  rational points of the intrinsic root subgroup.
- `ChevGroup.rootCoordEquiv j` composes the two. It gives field coordinates on
  the rational root group, and `rootCoordEquiv_apply_coe` states that the
  coordinate `s` corresponds to the image under `G.u j` of the rational point
  attached to `s`.

## Provenance and scope

The results are an internal deduction from the published split existence
construction and the published monic root parametrization criterion. The
classical content is that the root groups of a Chevalley group are the images
of its root exponentials (Steinberg, *Lectures on Chevalley groups*, §3). The
unit constructs no valuation, commutator estimate or Weyl group relation. It
does not transport the structure to other split groups.
