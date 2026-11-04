# Rational points of dynamic unipotent subgroups in unipotent normal subgroups

Authors: Worker 266 (draft statement and Markdown) and Worker 1529 (source and
interface check, Markdown revision), for task `78895528-a2ff-490b-a6dd-816ced8667eb`.

`Langlands.GroupScheme.PseudoReductiveRationalUnipotentPointStatement.{u}` is a
Prop-valued statement. This module defines the proposition and proves nothing; a proof is
the subject of a separate task.

## Statement

Fix a universe `u`, fields `k K : Type u` with `[Algebra k K]` (an arbitrary field
extension, not necessarily algebraic, separable or algebraically closed), and write `b`
for `Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k`. The proposition
quantifies over:

- an actual group scheme `G : GroupScheme (Spec (CommRingCat.of k))` with
  `IsPseudoReductive G` (smooth, affine and connected over `k`, with trivial
  `k`-unipotent radical, `HasTrivialUnipotentRadical G`);
- an actual cocharacter `χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G`;
- an actual group scheme `H` over `Spec (CommRingCat.of K)` and a homomorphism
  `j : H ⟶ (GroupScheme.baseChange b).obj G` into `G_K` with `IsClosedSubgroup j` (the
  underlying morphism is a closed immersion), `IsUnipotent H` (every nonzero
  finite-dimensional representation has a nonzero fixed vector), and
  `(SubgroupFunctor.range j).IsNormal` (the points of `H` form a normal subgroup of the
  points of `G_K` on every test scheme over `K`). No smoothness, reducedness or
  connectedness of `H` is assumed;
- a rational point `u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X` with
  `u ∈ (Dynamic.unipotent χ).carrier _`, that is, `u ∈ U_G(χ)(k)`: the orbit map
  `t ↦ χ(t) u χ(t)⁻¹` extends from `𝔾_m` to `𝔸¹` with value `1` at `0`.

Assume that the base change of `u` to `K` lies in `H`: some `K`-point `y` of `H.X`
satisfies

```lean
baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G
    (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (y ≫ j.hom.hom) = toUnit _ ≫ u
```

Here `baseChangePointsEquiv b G T` is the pullback adjunction on points: it identifies
morphisms `T ⟶ G_K` over `Spec K` with morphisms `(Over.map b).obj T ⟶ G.X` over
`Spec k`. For `T` the `K`-point `Over.mk (𝟙 _)`, the left side is the `K`-point
`y ≫ j.hom.hom` of `G_K` viewed as the morphism `Spec K → G` over `k`. On the right,
`toUnit _` is the structure morphism from `Spec K` (over `k`) to the terminal object
`Over.mk (𝟙 (Spec k))`, so `toUnit _ ≫ u` is the `K`-valued point
`Spec K → Spec k → G` induced by `u`. The condition thus says `u_K ∈ H(K)` inside
`G_K(K) = G(K)`.

The conclusion is `u = 1`, the identity point of `G(k)`.

## Provenance

Source: Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
registered as `conrad-gabber-prasad-2015-pseudo-reductive` (file SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`; PDF page = printed
page + 26).

Proposition C.1.6 (printed p.586, PDF p.612) states that `G/P` is pseudo-complete for a
smooth connected affine `G` and a pseudo-parabolic `k`-subgroup `P`. Its proof reduces to
pseudo-reductive `G` over `k = k_s`, writes `P = P_G(λ)`, sets `G' = G_{k̄}^{red}` and
identifies `U = U_G(-λ)` with a dense open subscheme of `G/P`. On printed p.587 (PDF
p.613) it considers the quotient map `U_{k̄} → U'` and states: "The kernel of this map has
no nontrivial points of `U(k)`. Indeed, this kernel is contained in `R_u(G_{k̄})`, so if
it contains a nontrivial element of `U(k)` then it would contain infinitely many such
elements due to `T(k)`-equivariance (since `U = U_G(-λ)`), contradicting
pseudo-reductivity of `G` over `k`."

This statement is a derived generalization of that step, not a numbered result of the
source. The source step is the instance `χ = -λ`, `K = k̄` and `H = R_u(G_{k̄})` with `j`
its inclusion (a smooth connected unipotent normal closed subgroup of `G_{k̄}`), with
`k` separably closed: a point `u ∈ U(k)` in the kernel has `u_{k̄} ∈ R_u(G_{k̄})(k̄)`, and
the conclusion `u = 1` is the source's claim. The Lean form allows any field `k`, any
extension `K/k` and any closed unipotent subgroup `H` of `G_K` that is normal on every
test scheme.

A proof route (outline only; nothing here is proved): since `u ∈ U_G(χ)(k)`, the map
`s ↦ χ(s) u χ(s)⁻¹` extends to `c : 𝔸¹_k → G` with `c(0) = 1` and `c(1) = u`. The
image of `(g, s) ↦ g c(s) g⁻¹` on `G × 𝔸¹` passes through `1` and generates a smooth
connected normal `k`-subgroup `N`. Over `K` this map lands in `H`: on `G_K × 𝔾_m` by
normality of `H`, and on `G_K × 𝔸¹` because `H` is closed and `G_K × 𝔾_m` is
schematically dense. So `N_K ⊆ H` is unipotent, hence `N` is unipotent, and
pseudo-reductivity of `G` forces `N = 1`, so `u = c(1) = 1`.
