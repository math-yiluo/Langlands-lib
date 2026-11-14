# Assembly of the linear system over a locally noetherian base

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemGluing`.

- `prop_pullback_snd_comp`: a morphism property stable under base change and isomorphisms passes
  from `l'` to `pullback.snd (l' ≫ a) V.ι` when `a` is an open immersion with image `V`.
- `exists_local`: for `T` locally noetherian, `g : Y ⟶ T` proper, flat, geometrically integral and
  `M` invertible, every affine open `V` carries a universal family of the linear system of
  `[M]` over `V` (`LinearSystemCechModule.exists_affine_universal` for the base change of `g` to
  `Spec Γ(T, V)`, transported by `IsUniversalOn.transport`), with proper structure map over `V`.
- `LocalFibreFlatness`: the proposition that, for every such `g`, `M`, affine open `V` and universal
  family `(P, l, W)` over `V` with `P` locally noetherian, vanishing of `H¹(Y_t, M_t)` for all
  `t ∈ V` makes `pullback.snd l V.ι` flat and locally of finite presentation, and nonvanishing of
  `H⁰(Y_t, M_t)` for all `t ∈ V` makes it moreover surjective. It is an auxiliary definition of this
  proof, proved in `LinearSystemFlatness`.
- `nonempty_iso_of_class`, `class_of_nonempty_iso`: class equations `[O(E)] = [M] + [N]`
  are equivalent to isomorphisms `O(E) ≅ M ⊗ N` (W22's `icl` lemmas).
- `properFlatIntegralLinearSystem_of_localFibreFlatness`: `LocalFibreFlatness` implies
  `ProperFlatIntegralLinearSystemStatement`. The local families over all affine opens are glued
  (`LinearSystemGluing`); `Λ := glued`, `l := lG`, `W := Wd`, `N` the line bundle representing the
  class `n` of `glued_class`; properness, flatness, local finite presentation and surjectivity of
  `l` are local on `T` (`glued_prop`).
