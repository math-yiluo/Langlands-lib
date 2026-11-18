# Base change of the split Cayley automorphism group scheme

Notation as in `Points.md`: for a field `K`, `Aut_K` is the automorphism group scheme of Zorn's
split Cayley algebra over `K`, a closed subgroup scheme of `GL₈`. Let `K'` be a second field in the
same universe and `b : Spec K' ⟶ Spec K` any morphism of schemes.

- `automorphismSubgroup_split_eq`: for a commutative ring `A` with ring homomorphisms `K → A` and
  `K' → A`, the automorphism subgroups of `GL₈(A)` defined by the split datum over `K` and over
  `K'` are equal. Both consist of the matrices that fix Zorn's unit and preserve Zorn's product,
  and Zorn's structure constants are integers, so they do not depend on the base field.
- `baseChangeModelPointsEquiv b T`: for every scheme `T` over `K'`, the group of `T`-points of the
  base change of `Aut_K` along `b` is isomorphic to the group of `T`-points of `Aut_K'`. It is the
  composite of the published base-change points equivalence `baseChangePointsEquiv`, the
  description of the points of `Aut_K` by automorphism matrices (`pointsEquiv`, with `T` viewed
  over `K` via `b`), the equality above, and the inverse of the same description for `Aut_K'`.
  `pointsEquiv_baseChangeModelPointsEquiv` states that it does not change the underlying
  automorphism matrix, and `baseChangeModelPointsEquiv_naturality` states that it is natural in
  `T`.
- `baseChangeModelIso b`: the resulting isomorphism of group schemes over `K'` between the base
  change of `Aut_K` along `b` and `Aut_K'`, built from the natural points equivalence with the
  published `isoOfPoints`. `pointsEquiv_baseChangeModelIso_hom` states that on every test scheme
  it preserves the automorphism matrix.

This isomorphism is internal to this development. It is used to reduce connectedness and the
triviality of the geometric unipotent radical of `Aut_K` to the algebraically closed field case.
It follows the pattern of the published base-change isomorphism `baseChangeModelIso` for
orthogonal matrix group schemes.
