# Herbrand functions and upper ramification groups without completeness

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be an extension of discretely valued fields in which the valuation of `K` extends uniquely to `L` (hypothesis `huniq`). The file attaches the Herbrand function `φ`, its inverse `ψ` and the upper ramification groups to the real lower ramification groups `G_s` of `Gal(L/K)` defined in the companion file. Neither field is assumed complete; the valued-field inputs are the instance that the valuation of `L` extends that of `K`, and `huniq`.

## Main definitions and results

- `lowerRamificationFiltrationOfUniqueExtension huniq`: the integral levels `n ↦ G_n` as an antitone filtration of `Gal(L/K)` by normal subgroups. The file's comment calls it the general replacement for a filtration that exists elsewhere in the library only for complete fields.
- `herbrandFunctionOfUniqueExtension huniq` and `inverseHerbrandFunctionOfUniqueExtension huniq`: `φ` and `ψ`, the library's group-theoretic Herbrand function of this filtration and its inverse, as maps `ℝ → ℝ`.
- `herbrandFunctionOfUniqueExtension_psi`, `inverseHerbrandFunctionOfUniqueExtension_eta`: `φ ∘ ψ = id` and `ψ ∘ φ = id`.
- `herbrandFunctionOfUniqueExtension_strictMono`, `inverseHerbrandFunctionOfUniqueExtension_strictMono`: both are strictly increasing.
- `upperRamificationGroupOfUniqueExtension huniq t`: the upper group at `t`, defined as the real lower group at `ψ(t)`.
- `upperRamificationGroupOfUniqueExtension_herbrandFunction`: the upper group at `φ(s)` is the lower group `G_s`.
- `inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff`: `ψ(t) ≥ −1` iff `t ≥ −1`.

All results restate general facts about the Herbrand function of an antitone normal filtration for this particular filtration.

## Points to watch

- `φ` and `ψ` are computed from the integral levels `G_n` only, while the upper groups are real lower groups evaluated at `ψ(t)`.
- The definitions take no separability hypothesis on the residue extension, although the docstring of `herbrandFunctionOfUniqueExtension` mentions one. `L/K` is not assumed Galois; `Gal(L/K)` is the group of `K`-automorphisms of `L`. Finiteness of `L/K` is declared after the filtration and applies to the results on `φ` and `ψ`; the lemmas unfolding the two definitions omit it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`: the Lean file is the source byte for byte (SHA-256 `672eaa7f2130b8ef6e0fa4c0737249ce73f888c60550d87dd9c5e000e0063589`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
