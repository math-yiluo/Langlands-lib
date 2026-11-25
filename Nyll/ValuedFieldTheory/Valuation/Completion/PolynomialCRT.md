# Chinese remainder theorem for polynomials as an algebra isomorphism

Module `Nyll.ValuedFieldTheory.Valuation.Completion.PolynomialCRT`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The algebraic step behind the decomposition of `K_v ⊗_K L`: if a polynomial over a field factors into pairwise coprime factors, the algebra obtained by adjoining a root of the product is the product of the algebras obtained by adjoining a root of each factor.

## Main definitions and results

- `quotientInfAlgEquivPiQuotient`: for a finite family of pairwise coprime ideals `Iᵢ` of a commutative `R`-algebra `A`, Mathlib's Chinese remainder ring isomorphism `A ⧸ ⨅ᵢ Iᵢ ≃ ∏ᵢ A ⧸ Iᵢ` is an `R`-algebra isomorphism.
- `adjoinRootProdEquivPi`: for a field `F`, a finite family of pairwise coprime polynomials `fᵢ ∈ F[X]`, the `F`-algebra isomorphism `AdjoinRoot (∏ᵢ fᵢ) ≃ ∏ᵢ AdjoinRoot fᵢ`.
- `adjoinRootProdEquivPi_mk`: this isomorphism sends the class of `g` to the family of classes of `g` modulo each `fᵢ`.

## Points to watch

The hypothesis is pairwise coprimality of the given factors, not squarefreeness of the product; irreducibility of the factors is not needed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/PolynomialCRT.lean`: the Lean file is the source byte for byte (SHA-256 `3353e95b6400fd8c3270b4839d7b0a10172f696701eb7f74d7bcacaa573ba19d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
