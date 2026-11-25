# Choosing prime elements

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For valuation data `v` on a `G`-module `A` in the abstract class field theory of the library, this file fixes a prime element in every field of finite absolute degree. It also records that two prime elements differ by a unit. The module is written additively, so a unit is an element of valuation zero.

## Main definitions and results

- `ValuationData.chosenPrimeElement v K`: an element of `A_K` of valuation `v.oneValue`. It is chosen with `Classical.choose`, using surjectivity of the normalized valuation (`normalizedValuation_surjective`).
- `valuationAt_chosenPrimeElement`, `chosenPrimeElement_isPrime`: this element has valuation `v.oneValue`, so it is a prime element.
- `sub_mem_unitAddSubgroup_of_prime`: if `π` and `π'` are prime elements of `K`, then `π' − π` lies in the unit subgroup.
- `sub_chosenPrimeElement_mem_unitAddSubgroup`: the special case of a prime element and the chosen one.

## Watch for

The chosen prime element is noncomputable and arbitrary. Results built on it, such as the definition of the reciprocity map, are made independent of the choice only elsewhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`: the Lean file is the source byte for byte (SHA-256 `465a13b06c2fea147fff13e1fa18692f3a03b049a89b91bdb71fce074d4646e3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
