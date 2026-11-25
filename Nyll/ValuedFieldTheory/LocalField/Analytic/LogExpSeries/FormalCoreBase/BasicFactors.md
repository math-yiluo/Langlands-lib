# Basic factors of X + Y + XY

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.BasicFactors`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file sets up the combinatorics behind the coefficients of `(X + Y + XY)^q` in two variables. Exponent vectors are elements of `Fin 2 →₀ ℕ`; only three of them carry a nonzero coefficient in `X + Y + XY`: the left vector (`X`), the right vector (`Y`) and the mixed vector (`XY`). A way of picking one monomial from each of `q` factors is recorded as a finitely supported sequence `l : ℕ →₀ (Fin 2 →₀ ℕ)` whose entries at positions `0, …, q - 1` are basic.

## Main definitions and results

- `formalLogOnePlusProductArgumentBasicFactor m`: the proposition that `m` is one of the three basic vectors. `formalLogOnePlusProductArgumentBasicFactorFinset` is the same set as a `Finset`, with membership lemma and cardinality `3`.
- `formalLogOnePlusProductArgumentBasicFactorLabel`: labels left, right and mixed by `0`, `1`, `2` in `Fin 3`, with simp lemmas on the three basic vectors and characterizations of labels `0` and `1`.
- `formalLogOnePlusProductArgumentBasicFactorProductChoices q`: sequences supported in `range q` with basic entries there; it has `3 ^ q` elements.
- `formalLogOnePlusProductArgumentBasicFactorChoices q e`: the sequences of `Finset.finsuppAntidiag (range q) e` (entries summing to `e`) whose first `q` entries are basic; there are at most `3 ^ q` of them.
- Counting functions: `formalLogOnePlusProductArgumentLeftChoiceCount`, `…RightChoiceCount`, `…MixedChoiceCount` count the left, right and mixed entries among the first `q`; `formalLogOnePlusProductArgumentBasicFactorLabelCount q l j` counts entries with label `j`. The left and right counts equal the label counts `0` and `1` for every `l`; the mixed count equals the label count `2` when the first `q` entries are basic.

The membership lemma for product choices is proved from `Finset.mem_finsupp_iff`, the other two by `simp`; the cardinality `3 ^ q` comes from `Finset.card_finsupp`.

## Points to watch

- The label function sends every non-basic vector to `2`, the mixed label. Statements that read a factor off its label `2` therefore carry a basic-factor hypothesis.
- Although the namespace is `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation`, the content is pure finite combinatorics, with no field or valuation.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalCoreBase/BasicFactors.lean`: the Lean file is the source byte for byte (SHA-256 `34fc66aad00b6090a36ab1f879bf9b3c5cb63986da974e01de1813403878bf83`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
