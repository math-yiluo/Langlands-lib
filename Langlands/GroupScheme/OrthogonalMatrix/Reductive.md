# The identity component of the split orthogonal group is reductive

This internal module proves that, over every field `K` and for an index type `l` with at
least two elements, the identity component of the split orthogonal group
`OrthogonalMatrix.groupScheme l K` (the orthogonal group of the hyperbolic form
`Q(x, y) = Σ_a x_a y_a` on `K^{l ⊕ l}`) has trivial unipotent radical, and hence is a
connected reductive group. The argument is the classical one: the fixed vectors of a
connected unipotent normal subgroup form a nonzero subspace of the standard
representation that is stable under enough elements of the identity component, and the
standard representation is irreducible for those elements. The fixed-vector part follows
the published module `SymplecticMatrix.Reductive`; the irreducibility argument is new.

## Irreducibility of the standard representation

- `alt K a b`: the alternating matrix `E_{ab} - E_{ba}`; `isAlt_alt`,
  `alt_mulVec_apply_left` (coordinate `a` of `alt a b · x` is `x_b`, for `a ≠ b`) and
  `alt_mulVec_single` (`alt a b · e_b = e_a`).
- `upper_mulVec`, `lower_mulVec`: the block matrices `[[1, Y], [0, 1]]` and
  `[[1, 0], [Y, 1]]` (published `SymplecticMatrix.upper`, `SymplecticMatrix.lower`) send
  `v` to `v + (Y v₂, 0)` and `v + (0, Y v₁)`.
- `levi_mulVec_elim`: the Levi matrix `diag(A, A⁻ᵀ)` sends `(x, 0)` to `(A x, 0)`.
- `transvection_mulVec_sub`: `(1 + c E_{ab}) y - y = c y_b e_a`.
- `single_inl_eq`, `single_inr_eq`: basis vectors of `K^{l ⊕ l}` in block form.
- `eq_top_of_stable`: a nonzero subspace `W` of `K^{l ⊕ l}` that is stable under all Levi
  matrices and all block matrices `upper Y`, `lower Y` with `Y` alternating is the whole
  space, when `l` has at least two elements. Proof: take `v ∈ W` nonzero. If `v₂ = 0` then
  `v = (v₁, 0)`; otherwise `v_{inr b} ≠ 0` for some `b`, and for `a ≠ b` the vector
  `upper(alt a b) v - v = (alt a b · v₂, 0)` is nonzero at `a`. So `W` contains some
  `(x, 0)` with `x ≠ 0`. Applying a Levi transvection `1 + E_{ab}` and subtracting gives
  `(x_b e_a, 0) ∈ W`; choosing `b` with `x_b ≠ 0` gives `(e_c, 0) ∈ W` for all `c ≠ b`,
  and one more transvection gives `(e_b, 0)`. Finally
  `lower(alt c b') (e_{b'}, 0) - (e_{b'}, 0) = (0, e_c)` for `b' ≠ c`. So `W` contains
  the standard basis.

## Fixed vectors of normal subgroups of the identity component

- `mulVec_mem_fixedSubmodule`: if conjugation by the constant point of `g ∈ O(K)`
  preserves the points of `H` (mapped into the orthogonal group by `j`), then `g`
  preserves the vectors fixed by `H` in the standard representation (published
  `MatrixRepresentation.fixedSubmodule`).
- `pointsEquiv_eq_one`: if `H` is unipotent and every `g ∈ O(K)` whose constant points
  lie in the identity component normalizes `H` in this sense, then every point of `H`
  acts as the identity matrix. The fixed subspace is nonzero (unipotence), stable under
  the Levi and block matrices, whose constant points lie in the identity component
  (`constantPoint_levi_mem`, `constantPoint_upper_mem`, `constantPoint_lower_mem` from
  `OrthogonalMatrix.Subgroups`), so it is everything by `eq_top_of_stable`.
- `hasTrivialUnipotentRadical_identityComponent l K`: every smooth connected unipotent
  normal closed subgroup of the identity component is trivial. Normality in the identity
  component gives the conjugation hypothesis of `pointsEquiv_eq_one`, since the constant
  point of such a `g` is a point of the identity component; the subgroup's points then
  map to `1`, and the inclusion of the identity component is a monomorphism.
- `isConnectedReductive_identityComponent l K`: the identity component is a connected
  reductive group. It is smooth, affine and connected (`OrthogonalMatrix.Subgroups` and
  the published identity component API); its base change to an algebraic closure is
  identified with the identity component of the model over the algebraic closure
  (published `IdentityComponent.baseChangeIso` and `IdentityComponent.mapIso` applied to
  `baseChangeModelIso`), which has trivial unipotent radical by the previous theorem.
