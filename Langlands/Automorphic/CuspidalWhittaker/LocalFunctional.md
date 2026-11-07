# A local Whittaker functional on an embedded cuspidal local component

Author: Worker 1709.

This is internal infrastructure for the proof of
`Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement`. It turns the global
Whittaker coefficient of `WhittakerCoefficient` into a nonzero local functional on an actual
local realization. All results are proved, with no hypothesis beyond
`CompactSpace (AdeleQuotient F)`.

## Setting

`S : LocalRealization F (r + 1) v` is a `GL_{r+1}(F_v)`-stable subspace of the Library's
automorphic forms, acting by right translation through `localInclusion` and
`AdelicGL.ofFinite`. `S.IsCuspidal` means that every form in `S` is cuspidal. The module
activates the Library's named local `AddCommGroup` instances
(`localRealization*AddCommGroup`), so the linear structures agree with those of
`LocalRealization`.

## Entries of local elements

For `u ∈ GL_{r+1}(F_v)`, let `ι_v(u) = AdelicGL.ofFinite (localInclusion v u)`. Its entries are
as follows (`ofFinite_localInclusion_eq_one`, `ofFinite_localInclusion_offDiag`):

- if `u_{ij}` equals the identity entry, so does `ι_v(u)_{ij}`;
- off the diagonal, `ι_v(u)_{ij}` is the finite adele `finiteSingle v (u_{ij})`.

Hence, for `u` in the Library's `upperUnipotent (r + 1) (FiniteCompletion F v)`:

- `isUpperColId_ofFinite`: `ι_v(u)` satisfies `IsUpperColId 0`.
- `superSum_ofFinite`: `superSum 0 (ι_v(u)) = finiteToAdeles (finiteSingle v (Σᵢ u_{i,i+1}))`.

`ofFinite_localInclusion_commute`: an adelic `h₀` whose `v`-component is `1` commutes with
every `ι_v(u)`. This is checked componentwise at each finite place, using `localProjection`.

## The functional

- `levelProps_form`: for cuspidal `S` and `x ∈ S`, `LevelProps r (evaluate (S.toContinuous x))`.
  This is `levelProps_top` with the Library's `LocalRealization.constantTerm_eq_zero`.
- `descend_representation`: `W_{π(g)x}(a) = W_x(a ι_v(g))`. It follows from
  `LocalRealization.evaluate_representation` and `descend_mul_right`.
- `exists_trivial_at_mul`: every `g₀ ∈ GL_{r+1}(𝔸_F)` is `h₀ ι_v(g_v)` with `h₀` trivial at
  `v`. Take `g_v` to be the `v`-component of `g₀`.
- `whittakerFunctional S hS h₀ : Module.Dual ℂ S.Space` is `x ↦ W_x(h₀)`, where
  `W_x = descend r (evaluate (S.toContinuous x))`. Linearity comes from `descend_add` and
  `descend_const_mul`.
- `whittakerFunctional_equivariant`: if `h₀` is trivial at `v`, then for
  `u ∈ upperUnipotent (r + 1) (FiniteCompletion F v)`,

  ```text
  ℓ(π(u) x) = W_x(h₀ ι_v(u)) = W_x(ι_v(u) h₀) = χ_v(Σᵢ u_{i,i+1}) ℓ(x).
  ```

  The last step is `Equivariant 0` at level `0` together with `superSum_ofFinite` and
  `localCharacter_apply`.
- `whittakerFunctional_ne_zero`: if `W_x(h₀ ι_v(g_v)) ≠ 0`, then `ℓ ≠ 0`, because
  `ℓ(π(g_v) x) = W_x(h₀ ι_v(g_v))`.

## Main result

`exists_localWhittakerFunctional`: if `S` is cuspidal and `S ≠ ⊥`, there is a nonzero
`ℓ : Module.Dual ℂ S.Space` with

```text
ℓ(S.representation u x) = (localCharacter F v (Σ_{i : Fin r} u_{i.castSucc, i.succ}) : ℂ) * ℓ x
```

for all `u ∈ upperUnipotent (r + 1) (FiniteCompletion F v)` and `x ∈ S.Space`. The proof runs
as follows.

1. Choose `x₀ ≠ 0` in `S` (`exists_ne_zero_of_ne_bot`). Its underlying function is nonzero
   somewhere (`exists_evaluate_ne_zero`).
2. By `exists_descend_ne_zero`, `W_{x₀}(g₀) ≠ 0` for some `g₀`.
3. Write `g₀ = h₀ ι_v(g_v)` with `h₀` trivial at `v`, and take
   `ℓ = whittakerFunctional S hS h₀`.

This is exactly the input format of the published
`LocalRealization.isGeneric_of_integerTrivial_character`.
