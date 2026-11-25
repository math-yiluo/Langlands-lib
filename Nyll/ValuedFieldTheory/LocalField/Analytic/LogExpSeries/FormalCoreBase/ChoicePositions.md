# Choices of basic factors from position sets

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoicePositions`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A choice of basic monomials in `(X + Y + XY)^q` is determined by where the mixed factors `XY` and the left factors `X` sit: every other position below `q` holds a right factor `Y`. This file builds a choice from two position sets, extracts the position sets from a choice, and checks that the two operations match.

## Main definitions and results

- `formalLogOnePlusProductArgumentBasicFactorLeft`, `…Right`, `…Mixed`: names for the three basic exponent vectors.
- `formalLogOnePlusProductArgumentBasicFactorLabel_eq_two_iff_of_basic`: for a basic vector, the label is `2` exactly when it is the mixed vector.
- `formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L`: the sequence that is mixed on `M`, left on `L` outside `M`, right on the remaining positions below `q`, and zero from `q` on; two simp lemmas give its values.
- `formalLogOnePlusProductArgumentMixedPositions q l`, `…LeftPositions`, `…RightPositions`: the positions below `q` with label `2`, `0`, `1`. Their cardinalities are the corresponding label counts.
- Round trip: the mixed positions of `ChoiceFromMixedLeft q M L` are `M` when `M ⊆ range q`; its left positions are `L` when `L ⊆ range q \ M`; under the same hypothesis its right positions are `range q \ (M ∪ L)`.
- `formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft_card`: if `M ⊆ range q` has `a + b - q` elements, `L ⊆ range q \ M` has `q - b` elements, and `a ≤ q`, `b ≤ q`, `q ≤ a + b`, then there are `q - a` right positions.

The round-trip statements are proved pointwise by cases on membership in `M` and `L`; the count uses disjointness of `M` and `L` and `omega`.

## Points to watch

- Where `M` and `L` overlap, `M` wins; the round-trip results need the subset hypotheses `M ⊆ range q` and `L ⊆ range q \ M`.
- Position sets are defined through labels, so a non-basic entry is counted as mixed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalCoreBase/ChoicePositions.lean`: the Lean file is the source byte for byte (SHA-256 `39af0c72ab1bbfe2137d7d2dc518745138c099492540ed1bb4a4c26168146084`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
