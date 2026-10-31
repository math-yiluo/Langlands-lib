# The subsheaf of `p_* 𝒪_X` cut out by a unit cocycle

This helper module supports the proof of
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement`. It defines the sheaf of
modules `L` on `Y` that the proof shows to be the descended line bundle. The definitions are
internal and have no separate literature source. They follow the classical construction of
the descended module as the submodule of `S` cut out by a descent datum (Stacks Project,
Descent, Tag 023N), sheafified over the opens of `Y`. Everything lives in the namespace
`Langlands.Scheme.UnitCocycleDescent`.

Fix a morphism `p : X ⟶ Y` and a family `c` that assigns a unit `c U a b h` of `Γ(U, ⊤)` to
every scheme `U` and pair `a b : U ⟶ X` with `h : a ≫ p = b ≫ p`. No compatibility of `c`
is assumed in this module.

## Pullbacks along pairs over `Y`

- `preimage_preimage_eq`: for such a pair, `a ⁻¹ᵁ p ⁻¹ᵁ W = b ⁻¹ᵁ p ⁻¹ᵁ W` for every open
  `W` of `Y`.
- `appLE_app_eq`: for a function `r` on `W`, the sections `a.appLE (p ⁻¹ᵁ W) V ha (p.app W r)`
  and `b.appLE (p ⁻¹ᵁ W) V hb (p.app W r)` agree on every open `V` of `U`. Both sides are
  `(a ≫ p).appLE W V _ r` by `appLE_comp_appLE`, and `appLE_eq_of_eq` from
  `FunctionDescent` identifies the two composites.

## The cocycle condition

`IsCocycleSection p c W σ` says the following about a section `σ` of `𝒪_X` over
`p ⁻¹ᵁ W`. For every scheme `U`, every pair `a b : U ⟶ X` with `h : a ≫ p = b ≫ p`, every
open `V` of `U` and all inclusions `ha : V ≤ a ⁻¹ᵁ p ⁻¹ᵁ W`, `hb : V ≤ b ⁻¹ᵁ p ⁻¹ᵁ W`,

`(c U a b h)|_V * a.appLE (p ⁻¹ᵁ W) V ha σ = b.appLE (p ⁻¹ᵁ W) V hb σ`.

In words, `c` carries `a^* σ` to `b^* σ` on every open where both are defined. The condition
quantifies over arbitrary opens `V`, not only over `a ⁻¹ᵁ p ⁻¹ᵁ W`. The main proof then
compares sections of `a^* L` and `b^* L` over arbitrary opens directly with this condition.

The lemmas in the namespace `IsCocycleSection` show:

- `zero`, `add`: the condition holds for `0` and is closed under addition.
- `mul`: if `σ` satisfies it and `τ` has equal pullbacks along every pair, then `τ * σ`
  satisfies it.
- `app_mul`: `p.app W r * σ` satisfies it when `σ` does, by `mul` and `appLE_app_eq`.
- `map`: the condition is preserved by restriction to a smaller open `W' ≤ W`. The proof
  uses `Scheme.Hom.map_appLE`.
- `of_locally`: the condition is local on `Y`. Suppose every point `y` of `W` has an open
  neighbourhood `W' ≤ W` on which the restriction of `σ` satisfies the condition. Given a
  pair and an open `V`, cover `V` by the opens `V ⊓ a ⁻¹ᵁ p ⁻¹ᵁ W'`, one for each point of
  `V`. Since the structure sheaf of `U` is separated (`TopCat.Sheaf.eq_of_locally_eq'`), it
  suffices to check the equation on each of these opens, where it is the hypothesis
  (rewritten with `map_appLE` and `appLE_map`).

## The sheaf of modules `L`

- `pushforwardUnit p` is the pushforward `p_* 𝒪_X` of the structure sheaf of `X`, a sheaf
  of modules on `Y`. Its sections over `W` are `Γ(X, p ⁻¹ᵁ W)`.
- `pushforwardUnit_smul`: a function `r` on `W` acts on these sections by multiplication
  with `p.app W r`. This holds by definition (`rfl`).
- `cocyclePresheafSubmodule p c` is the presheaf of submodules of `p_* 𝒪_X` whose sections
  over `W` are those satisfying `IsCocycleSection p c W`. It is closed under the module
  operations by `zero`, `add` and `app_mul`, and under restriction by `map`.
- `cocycleSubmodule p c` is the same family as a `SheafOfModules.Submodule` of
  `p_* 𝒪_X`, Mathlib's notion of a subsheaf of modules
  (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule`). The sheaf condition asks that a
  section that lies locally in the submodule lies in it. This is `of_locally`.
- `cocycleModule p c` is the sheaf of modules `L` underlying `cocycleSubmodule p c`.
