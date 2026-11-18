# Connectedness of the split Cayley automorphism group scheme

Notation as in `Points.md`: for a field `k`, `Aut_k` is the automorphism group scheme of Zorn's
split Cayley algebra over `k`, a closed subgroup scheme of `GL₈`.

- `isAutomorphism_map_ringEquiv`: changing the coefficients of an automorphism matrix along a
  ring isomorphism `f : A ≃ B` gives an automorphism matrix. Zorn's unit has entries `0` and `1`,
  and Zorn's product commutes with ring homomorphisms (`map_mulFun`).
- `connectedSpace_automorphismGroup_of_isAlgClosed`: if `k` is algebraically closed, `Aut_k` is
  connected. `Aut_k` is smooth and affine (`smooth_automorphismGroup`), so by the published
  `IdentityComponent.connectedSpace_of_forall_mem_range` it is enough to show that every
  `k`-point lies in the identity component. Let `Γ` be the ring of global sections of `Spec k`,
  identified with `k` by `e : k ≃ Γ`.
  - Every root element `x_α(c)` with `c ∈ Γ` is the image of a `Γ`-point of the additive group
    under the root homomorphism `rootMap k α`. Every torus element with parameters `s, t ∈ Γˣ` is
    the image of a point of the rank-two split torus under `torusMap k`. The additive group and
    the split torus are connected. So by the published
    `SymplecticMatrix.comp_mem_range_identityComponentι` these points lie in the identity
    component.
  - Hence the subgroup `P` of `GL₈(Γ)` formed by the matrices of the points in the identity
    component contains the image of `rootTorusClosure k` under `e`.
  - A `k`-point `x` has an automorphism matrix `g` over `Γ`. Its transport `g₀` to `k` is an
    automorphism matrix, so it lies in `rootTorusClosure k` by `mem_rootTorusClosure`
    (`Generation.lean`). Therefore `g` lies in `P`. Since points are determined by their
    matrices, `x` lies in the identity component.
- `connectedSpace_automorphismGroup k`: for every field `k`, `Aut_k` is connected. The base
  change of `Aut_k` to an algebraic closure `k̄` is isomorphic to `Aut_k̄` (`baseChangeModelIso`),
  which is connected by the previous result. Connectedness descends along the surjective map
  `Spec k̄ → Spec k` (the published `connectedSpace_of_baseChange`).

The argument follows the published proof of connectedness of the split symplectic group
(`SymplecticMatrix.connectedSpace_groupScheme`), with the generation theorem of
`Generation.lean` in place of the big-cell decomposition.
