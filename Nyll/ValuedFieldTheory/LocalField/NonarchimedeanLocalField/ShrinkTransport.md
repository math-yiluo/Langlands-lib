# The universe-0 model of a nonarchimedean local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A nonarchimedean local field `K` in an arbitrary universe is small, so it has a copy `Shrink.{0} K` in universe `0`, with ring structure and topology transported by Mathlib along `Shrink.ringEquiv K`. This file transports the valuative relation as well and proves that the copy is again a nonarchimedean local field. It also gives two general lemmas on transporting extensions of valuations.

## Main definitions and results

- `smallLocalField K : Small.{0} K`, taken from the imported `nonarchimedeanLocalField_small`.
- `shrinkLocalFieldValuation`: the canonical valuation of `K` pulled back along `Shrink.ringEquiv K`; `shrinkLocalFieldValuativeRel` is the valuative relation it defines on `Shrink.{0} K`.
- `shrinkLocalField_valuation_lt_iff`: strict comparisons of valuations on the copy are those of the images in `K`.
- `shrinkLocalField_locallyCompact`, `shrinkLocalField_isNontrivial`, `shrinkLocalField_isTopologicalAddGroup`, `shrinkLocalField_isValuativeTopology`: the transported structures are locally compact, nontrivial, an additive topological group, and the topology is the valuative one.
- `shrinkLocalField_isNonarchimedeanLocalField`: hence `Shrink.{0} K` is a nonarchimedean local field.
- `hasExtension_comap_ringEquivs`: if `vF` extends to `vG` along `F → G`, and `F₀ ≃ F`, `G₀ ≃ G` are ring isomorphisms compatible with the algebra maps, then the pulled-back valuations satisfy `HasExtension` along `F₀ → G₀`.
- `hasExtension_of_isEquiv`: `HasExtension` is preserved when both valuations are replaced by equivalent ones.

## Proofs

The valuative topology is checked on neighbourhood bases of `0`: balls `{z | v z < v a}` with `a ≠ 0` correspond under the homeomorphism because the valuation is pulled back along the same isomorphism.

## Points to watch

- `shrinkLocalFieldValuativeRel` is a definition, not a global instance; the statements fix it (and `smallLocalField K`) by `let`, so they are about this specific model.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean`: the Lean file is the source byte for byte (SHA-256 `df11773005d26980ad0a1db99077b1d943d51ec966879d558b47f937c05a8f55`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
