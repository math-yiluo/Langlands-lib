# Herbrand's theorem for discretely valued fields

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandTheorem`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension with group G = Gal(L/K), carrying discrete valuations `base` on K and `target` on L (the library's `DVF` structures) with `target` extending `base`. For a normal subgroup H of G the file builds the ramification filtration of the fixed extension L^H/K and proves Herbrand's theorem: lower numbering passes to the quotient G/H after a change of variable by the Herbrand function of L/L^H, Herbrand functions compose in the tower K ⊆ L^H ⊆ L, and upper numbering passes to quotients unchanged. No completeness is used.

## Definitions

- `fixedFieldLowerRamificationFiltration`: the lower ramification groups of L^H/K at integer levels, as an antitone filtration by normal subgroups of Gal(L^H/K). Antitonicity and normality of the real-indexed groups `fixedFieldLowerRamificationGroup` are proved first.
- `fixedFieldHerbrandFunction`, `fixedFieldInverseHerbrandFunction`: the functions η and ψ of L^H/K built from that filtration. They are mutually inverse and strictly increasing, and ψ(t) ≥ −1 exactly when t ≥ −1.
- `fixedFieldUpperRamificationGroup H t`: the lower group of L^H/K at ψ(t).

## Main results

All four assume that the residue field extension is separable.

- `lowerRamificationGroup_quotient`: the image of G_s in G/H, identified with Gal(L^H/K), is the lower group of L^H/K at the value at s of η(L/L^H). Here η(L/L^H) is the Herbrand function of `fixedFieldSubextensionFiltration`, the filtration of G restricted to H.
- `herbrandFunction_trans`: η(L/K) = η(L^H/K) ∘ η(L/L^H) at every real s.
- `inverseHerbrandFunction_trans`: ψ(L/K) = ψ(L/L^H) ∘ ψ(L^H/K).
- `upperRamificationGroup_quotient`: the image of the upper group G^t in G/H is the upper group (G/H)^t.

## Proof

The ramification numbers of G are treated as an abstract nonarchimedean depth. An earlier coset-sum formula shows that the ramification number of a nontrivial element of G/H is `quotientFiberAverage`: the sum of the depths over its coset divided by the ramification index of L/L^H. A coset representative of maximal depth then decides membership in the image of G_s. Composition of η follows from the depth-sum formula for η, private averaging lemmas on truncated fibre sums, and the relation e(L/K) = e(L^H/K) · e(L/L^H) at level 0. For s < −1 each Herbrand function involved takes the value s.

## Watch for

- Uniqueness of the extension of the valuation is not derived. It is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target` in every definition and main result.
- The `DVF` structures, filtrations and Herbrand functions are the library's own, not Mathlib's. The filtrations are indexed by ℕ, and a real index s enters only through `realRamificationExponent s`, the least natural number n with s + 1 ≤ n.
- η(L/L^H) is obtained from the subgroup filtration of H, not from a valuation on L^H.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandTheorem.lean`: the Lean file is the source byte for byte (SHA-256 `05066ddcd8d8fa9b3d61e1e158ce46ec38b729b201500495fb5138611b843e23`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
