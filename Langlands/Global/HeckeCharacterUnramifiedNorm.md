# Unramified values of norm-composed Hecke characters

Worker 5130 wrote this module for Task 7784. It evaluates the Hecke character `χ ∘ N_{L/K}`
(the published `HeckeCharacter.normComp`) at a uniformizer of an unramified completion.

## Statements

In namespace `Langlands.Global.HeckeCharacter`:

- `mem_units_of_valued_eq_one`: a unit of `K_p` of valuation one lies in the unit group of
  the valuation ring, in the form used by `HeckeCharacter.IsUnramifiedAt`.
- `finiteComponent_eq_of_valued_eq`: if `χ` is unramified at `p` (trivial on the units of
  the valuation ring of `K_p`), then `χ_p` takes the same value on two units of `K_p` of
  equal valuation. Their quotient is a valuation unit.
- `normComp_finiteComponent_uniformizer`: let `K` and `L` be number fields in one universe,
  `p` a finite place of `K`, and `q` a place of `L` above `p` with ramification index
  `e(q|p) = 1`. Let `χ` be a Hecke character of `K` unramified at `p`, `π` a uniformizer of
  `L_q` and `ϖ` a uniformizer of `K_p` (valuation `exp (-1)`). Then
  `(χ ∘ N_{L/K})_q(π) = χ_p(ϖ) ^ f(q|p)`.

The last proof uses the published `normComp_finiteComponent`:
`(χ ∘ N)_q(π) = χ_p(N_{L_q/K_p} π)`. The image `ϖ'` of `ϖ` in `L_q` has valuation
`exp (-1) ^ e = exp (-1)` (`valuation_completionMap`), so `π = ϖ' ε` with `ε` a valuation
unit. The local norm of `ϖ'` is `ϖ ^ [L_q : K_p] = ϖ ^ (e f) = ϖ ^ f`
(`localNorm_algebraMap`, `localDegree_eq`). The local norm of `ε` is a unit of the valuation
ring (`localUnitNorm_integral`), so `χ_p` is trivial on it.

## Provenance

Standard local class field theory computation (the norm of a uniformizer in an unramified
extension of degree `f` has valuation `f`). Internal to the project.
