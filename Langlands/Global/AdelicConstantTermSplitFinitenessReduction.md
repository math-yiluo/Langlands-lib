# Finiteness under the positive split component from Harish-Chandra's finiteness theorem

Module `Langlands.Global.AdelicConstantTermSplitFinitenessReduction` proves

```
constantTermSplitComponentFiniteness_of_parabolicHarishChandraFiniteness :
  ParabolicHarishChandraFinitenessStatement.{u} → ConstantTermSplitComponentFinitenessStatement.{u}
```

that is, finiteness of the left translates of `C_{U'}φ` by the positive split component
`𝔄_{P'}` (Bernstein–Lapid §6.2 and §8.5, Mœglin–Waldspurger I.3.2; module
`AdelicConstantTermSplitFinitenessStatement`) follows from Harish-Chandra's finiteness theorem on
`U'(𝔸)M'(F) \ G(𝔸)` (module `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement`).
The module does not prove `ParabolicHarishChandraFinitenessStatement`; it is a hypothesis of the
theorem. The module also contains three auxiliary results used in the proof.

## Auxiliary results

- `Langlands.GroupScheme.IsRationalLeviSubgroup.isIso_subgroupMultiplication_of_radical`: for a
  rational Levi subgroup `l : L → P` and any geometric unipotent radical `r : U → P`,
  multiplication `L × U → P` is an isomorphism. `IsRationalLeviSubgroup` supplies this for one
  radical `r₀`; `IsUnipotentRadical.range_eq` gives `range r₀ = range r`, and
  `IsClosedSubgroup.sourceIsoOfRangeEq` an isomorphism `e : U₀ ≅ U` with `e ≫ r = r₀`. The
  multiplication for `r₀` is that for `r` precomposed with the isomorphism `L × e`.
- `Langlands.Automorphic.GroupSchemeFunctions.plotSmoothEnvelopingAction_leftTranslation`: the action of the enveloping algebra on
  plot-smooth functions on `G(F_∞)` commutes with left translation (induction on the tensor
  algebra, from `plotSmoothDifferential_leftTranslation`). Consequently
  `centerAction_leftTranslate_eq_zero`: an element of the center that annihilates every infinite
  slice of `ψ` annihilates every infinite slice of `g ↦ ψ(x g)`, since that slice at `b` is the
  left translate by `x_∞` of the slice of `ψ` at `x_f b`.
- `exists_finiteDimensional_profile`: if the right translates of `ψ` by a subgroup `Kinf` of
  `G(F_∞)` span a finite-dimensional space `W`, the functions `k ↦ ψ(g k)` on `Kinf`, for all
  `g ∈ G(𝔸)`, lie in one finite-dimensional space `E`. With a basis `(w_i)` of `W`, write the
  translate of `ψ` by `k` as `∑_i c_i(k) w_i`; then `k ↦ ψ(g k)` is `∑_i w_i(g) c_i`, so `E` is the
  span of the coordinate functions `c_i`.

## Proof of the reduction

Take the data of `ConstantTermSplitComponentFinitenessStatement`, with `K_∞` the points `a` of
`G(F_∞)` with `(a, 1) ∈ K`, and let `ψ = C_{U'}φ`.

1. `ψ` is automorphic on `U'(𝔸)M'(F) \ G(𝔸)` for `K_∞` and `rho`, by
   `IsAutomorphicFunctionOn.subgroupConstantTerm_of_range_le` (module
   `AdelicParabolicConstantTermAutomorphy`) applied to `P' ⊆ P`. Fix an open subgroup `L` of
   `G(𝔸_f)` fixing `ψ`, an ideal `J` of finite codimension of the center annihilating the infinite
   slices of `ψ`, and the space `E` of `exists_finiteDimensional_profile` for `ψ`.
2. `ParabolicHarishChandraFinitenessStatement`, applied to `p'`, `iU'`, `l'` (multiplication
   `M' × U' → P'` is an isomorphism by the first auxiliary result), the maximal compact subgroup
   `K` with `P'(𝔸)K = G(𝔸)`, `rho`, `J`, `L` and `E`, gives a finite-dimensional span of the set
   `X` of automorphic functions on `U'(𝔸)M'(F) \ G(𝔸)` fixed by `L`, annihilated by `J` and with
   all `k ↦ f(g k)` in `E`.
3. Every translate `ψ_x : g ↦ ψ(x g)`, `x ∈ positiveCentralTorusPoints T i (l' ≫ p')`, lies in
   `X`:
   - `x = i(t)` for a point `t` of `T(𝔸)`, and `i = τ ≫ l' ≫ p'`, so `x` is the image of the point
     `y = (τ ≫ l')(t)` of `P'(𝔸)`. Conjugation by `x` preserves `U'(𝔸)`
     (`conj_mem_adelicPoints_range`, as `U'` is normal in `P'`), and `x` commutes with `M'(F)`
     because it lies in the centralizer of the image of `M'(𝔸)`. Hence `ψ_x` is left invariant
     under `U'(𝔸)` and `M'(F)`, and so under `parabolicQuotientSubgroup F p' iU' l'`. The other
     automorphy conditions hold by `IsAutomorphicFunctionOn.leftTranslate`.
   - Left translation commutes with right translation, so `L` fixes `ψ_x`, and
     `k ↦ ψ_x(g k) = ψ((x g) k)` lies in `E`.
   - `J` annihilates the infinite slices of `ψ_x` by `centerAction_leftTranslate_eq_zero`.
4. The span of the translates is contained in the span of `X`, hence finite-dimensional.

## Provenance

This is the route of Mœglin–Waldspurger I.2.17, printed p. 38 (chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`), which states that Harish-Chandra's
finiteness theorem extends to automorphic forms on `U(𝔸)M(k)\G`, combined with the observation
that left translation by the positive split component of `M'` preserves the level, the
annihilating ideal of `𝔷` and the `K`-types. Bernstein–Lapid §8.2, Lemma (p. 222) uses the
finiteness theorem in the same way for intertwining operators; Bernstein–Lapid §6.2 (p. 201) and
§8.5 (p. 224) use the finiteness of the translates of `C_{P,P'}φ` for the decomposition (6.3) and
the difference operators.
