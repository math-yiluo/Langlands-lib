# The `K`-side: from a unipotent normal subgroup of `G_K` to the rational side

Module `Langlands.GroupScheme.Reductive.RadicalFieldExtension.KSide`.

This module is an internal step in the proof of
`Langlands.GroupScheme.AlgebraicallyClosedRadicalFieldExtensionStatement`. It contains no new
definitions or statements from the literature. It proves the target from the rational-side
contradiction `RationalSideStatement` (module `RationalSideInterface`), which the module
`RationalSide` proves. The construction reuses the points and Hopf-algebra machinery of
`Langlands.GroupScheme.Absolute.BorelFieldExtension{Descent,Maximality}`.

## Results

- `pointMatrix_sub_one_pow_apply`: let `ρ` be a matrix representation of a group scheme `G`
  over `Spec R` and `M` its universal matrix (the matrix of `ρ` at the identity point
  `𝟙 G.X`). For every point `z : T ⟶ G` and all indices `a b`, the `(a, b)` entry of
  `(ρ(z) - 1)^m` is the pullback along `z` of the `(a, b)` entry of `(M - 1)^m`.
- `eq_one_of_ker_le`: for a Hopf algebra `H` over a field `k` and a `k`-algebra map
  `x : H → A`, if `x` kills the augmentation ideal (the kernel of the counit, written
  `(1 : WithConv (H →ₐ[k] k)).ofConv`), then `x` is the identity point.
- `hasTrivialUnipotentRadical_baseChange`: assume `RationalSideStatement.{u}`. Let `k ⊆ K` be
  algebraically closed fields in universe `u` and let `G` be a smooth affine group scheme
  over `Spec k` with `HasTrivialUnipotentRadical G`. Then the base change `G_K` along
  `Spec K → Spec k` has trivial unipotent radical. Connectedness of `G` is not needed.
- `algebraicallyClosedRadicalFieldExtensionStatement_of_rationalSide`:
  `RationalSideStatement.{u} → AlgebraicallyClosedRadicalFieldExtensionStatement.{u}`.

## Proof

- `pointMatrix_sub_one_pow_apply`: naturality of `pointMatrix` gives
  `ρ(z) = GL(z^*)(M)`. The ring map `z^*` on matrices commutes with subtraction of `1` and
  with powers.
- `eq_one_of_ker_le`: for `h ∈ H`, the element `h - ε(h)·1` lies in the augmentation ideal,
  so `x h = ε(h)`, which is the value of the identity point.

**The main theorem.** Let `H'` be a smooth connected unipotent group scheme over `Spec K` with
a closed subgroup `i : H' ⟶ G_K` whose range is normal. It must be shown that
`range i = ⊥`. Write `H` for the coordinate Hopf algebra of `G` over `k`. `K`-points of `G_K`
are `k`-algebra maps `H → K` (`extPointEquiv`).

1. *Setup.* `H'` is reduced, being smooth over a field. By `affineLinearEmbeddingStatement`,
   `G` has a closed-immersion representation `ρ : G → GL_N`. Let `M` be its universal matrix
   and `u(a, b) ∈ H` the `(a, b)` entry of `(M - 1)^N`, read in `H` through `coordEquiv`.
2. *The group `S`.* Let `S` be the group of `k`-algebra maps `H → K` whose `K`-point of `G_K`
   lies in the range of `i`. It is normal because `range i` is normal. It is solvable: the
   `K`-points of the unipotent group `H'` form a solvable group
   (`isSolvable_points_of_isUnipotent`), and `S` is their image.
3. *Members of `S` kill `u`.* Let `x ∈ S` come from a `K`-point `y` of `H'`. The composite
   `σ = i ≫ ρ_K ≫ (GL_N base change)` is a representation of `H'`. Since `H'` is unipotent,
   `(σ(y) - 1)^N = 0` (`pointMatrix_sub_one_pow_eq_zero_of_isUnipotent`). By
   `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom` and `baseChangePointsEquiv_comp`,
   `σ(y)` is `ρ` evaluated at the point of `G` attached to `x`. By
   `pointMatrix_sub_one_pow_apply` and `appTop_point`, its entries are `x(u(a, b))`.
4. *Points separate `K ⊗[k] H`.* `H` is smooth over `k` (`AffineCoordinates.smooth_algebra`),
   so `K ⊗[k] H` is reduced (`isReduced_of_smooth_of_domain`). Then
   `eq_zero_of_forall_extPoint` (module `Laws`) applies.
5. *The prime `Q`.* Let `Q ⊆ K ⊗[k] H` be the preimage under `theta` of the kernel of
   `i^*` (`BorelExistence.coordinateKernel`, a prime). An element `q` lies in `Q` exactly when
   every member of `S` kills it. For one direction, pull back along the `K`-points of `H'`.
   For the other, `H'` is reduced, so a function vanishing at every `K`-point is zero
   (`eq_zero_of_forall_point`). Every `K`-point of `H'` gives a member of `S`.
6. *`Q` lies over the augmentation ideal `P`.* By `eq_one_of_ker_le`, every point killing
   `P` is the identity, hence in `S`. Suppose some `q ∈ Q` has nonzero image in
   `K ⊗[k] (H/P)`. That ring is a domain (`isDomain_tensorProduct_of_isAlgClosed`), and of
   finite type over `K`. So some `K`-algebra map `φ` does not kill the image
   (`exists_algHom_ne_zero`). Its restriction `x` to `H` kills `P`, so `x ∈ S`. But
   `extPoint x` is `φ` composed with the map to `K ⊗[k] (H/P)`, so `x` does not kill `q`,
   contradicting step 5.
7. *Nontrivial case.* Suppose `1 ⊗ p ∉ Q` for some `p ∈ P`. Then the algebraic core
   `exists_isPrime_lt_of_normal_solvable` (module `Laws`) gives a prime `𝔭 < P` of `H` and a
   normal solvable group `Γ` of `k`-points that kill every `u(a, b)` and contain every
   `k`-point whose kernel contains `𝔭`. Transport `Γ` and `𝔭` to rational points of `G` and
   to `Γ(G, 𝒪)` along `rationalPointEquiv` and `coordEquiv`. The kernel of a rational point
   is computed by `rationalPointEquiv_left` and `ker_appTop_point`. A point `z ∈ Γ` acts
   unipotently in `ρ`: the entries of `(ρ(z) - 1)^N` are `z(u(a, b)) = 0`, by
   `pointMatrix_sub_one_pow_apply` and `appTop_point`. So these data satisfy the hypotheses
   of `RationalSideStatement`, which yields `False`.
8. *Trivial case.* Otherwise `1 ⊗ p ∈ Q` for every `p ∈ P`. By step 5, every member of `S`
   kills `P`, so it is the identity by `eq_one_of_ker_le`. Hence the `K`-points of `range i`
   lie in the range of the unit subgroup `kernelUnit`. `G_K` is separated and `K` is
   algebraically closed. So `SubgroupFunctor.range_le_of_algClosed_points` gives
   `range i ≤ range kernelUnit = ⊥` (`range_kernelUnit`), and `range i = ⊥`.

The final theorem unpacks the target proposition and applies the main theorem. It ignores the
hypothesis `ConnectedSpace G.X.left`.

## Correspondence with the sources

Conrad, *Reductive group schemes*, Exercise 3.4.1 (p.104), and Milne, *Algebraic Groups*,
Propositions 19.5 and 19.13 (pp.398–400), prove the result by spreading a nontrivial
unipotent normal subgroup of `G_K` out over a finitely generated `k`-subalgebra of `K` and
specializing at a `k`-point. This proof does the same with polynomial data instead of
schemes. The subgroup `H'` is recorded through its group `S` of `K`-points. Its normality,
solvability and unipotence in `ρ` become finitely many polynomial laws (module `Laws`).
These laws are spread out over a finitely generated `k`-subalgebra and specialized at a
`k`-point. Instead of the composition series with `G_a` quotients used by Conrad,
unipotence is recorded by the vanishing of the entries of `(ρ(g) - 1)^N`. On the `k`-side,
the module `RationalSide` rebuilds a subgroup scheme from the specialized group of rational
points.
