# Comparing the standard and multiplicative Lubin–Tate series over ℚ_p

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Over ℤ_p, with uniformizer `p`, there are two Lubin–Tate series: the standard one pX + Xᵖ and the multiplicative one (1 + X)ᵖ − 1. This file constructs the power series H with linear coefficient 1 that intertwines them, its reverse, and shows that H conjugates the standard scalar endomorphisms to the multiplicative ones. Evaluating H thus carries standard Lubin–Tate division points to multiplicative ones.

## Main definitions and results

- `padicStandardToMultiplicativeIntertwiner p`: the series H over the valuation ring of ℚ_p, obtained from the library's same-uniformizer recursion (`recursiveIntertwiner`) with linear coefficient 1. It has linear term X and no constant term (`_hasLinearTerm`, `_coeff_one`, `_hasSubst`).
- `padicStandardToMultiplicativeIntertwiner_intertwines` and `_functionalEquation`: (1 + H)ᵖ − 1 = H(pX + Xᵖ), i.e. the multiplicative series after H equals H after the standard series.
- `padicStandardToMultiplicativeIntertwiner_endomorphism`: for `a` in ℤ_p, H composed after the standard endomorphism [a] equals the multiplicative endomorphism with linear coefficient `a` (the recursive intertwiner of the multiplicative series with itself) composed after H.
- `padicMultiplicativeToStandardIntertwiner p`: the reverse series G, from the same recursion, with linear coefficient 1 and its own functional equation (`_intertwines`, `_functionalEquation`, `_hasSubst`).
- `padicStandardToMultiplicativeIntertwiner_subst_reverse` and `padicMultiplicativeToStandardIntertwiner_subst_reverse`: H ∘ G = X and G ∘ H = X.

## Proofs

The intertwining equations and linear terms of H and G come directly from the recursion, and the functional equations are their one-variable rewritings. The endomorphism identity and the two composition identities rest on the uniqueness statement `eq_of_hasLinearTerm_of_intertwines`: two series with the same linear term that intertwine the same pair of Lubin–Tate series are equal. Both sides of each of these identities are shown to intertwine the right series and to have the right linear term.

## Points to watch

- As the file says, H is constructed directly; the two formal group structures are not identified by comparing their kernels.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeIntertwiner.lean`: the Lean file is the source byte for byte (SHA-256 `cc10b1255f3c49b084162a36023e33b7761a09948c24a517c9f37bb895319661`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
