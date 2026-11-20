# Norm-trivial characters at the bottom prime step of a cyclic tower

`Langlands.Global.HeckeCharacter.CyclicPrimeNormCharacterRestrictionStatement`
concerns a tower `F ⊂ K ⊂ E` of cyclic Galois extensions with `[K : F] = p`
prime. A Hecke character `χ` of `K` trivial on the image of norms from `E`
is invariant under arithmetic pullback by every `K/F` automorphism. If
also `χ^p = 1` and `χ ≠ 1`, restriction along the actual idele-class inclusion
from `F` to `K` has kernel exactly the image of norms from `K` to `F`.
This is the character needed to apply the obstruction of Clozel–Rajan,
*Solvable base change*, Theorem 1, PDF p. 2, to a bottom prime step of the
corrected descent argument discussed at the end of §2, PDF p. 7. This
orientation of the tower is a derived application.

Write `N_E` and `N_K` for the norm images in the idele classes of `F`.
The norm tower gives `N_E ⊆ N_K`. The cyclic norm quotient has order
`[E : F]`, and the quotient `N_K / N_E` has order `[E : K]`. The norm from
`K` to `F` induces a surjection from the `E/K` norm quotient onto
`N_K / N_E`. Their equal orders make it an isomorphism. Thus `χ` is a
power of the norm pullback of a faithful character of the `E/F` quotient.
Invariance follows from the Galois product for the norm.

The composite of idele-class inclusion with the norm from `K` to `F`
is the `p`-th power map. On the cyclic `E/F` quotient, its image is the
index-`p` subgroup `N_K / N_E`. It follows that restriction to `F`
preserves the order of `χ` and factors through the cyclic `E/F` quotient.
If that order is `p`, the kernel in that quotient is the unique
index-`p` subgroup, yielding `HasNormKernel K`.

The norm-kernel character is the class-field character used in
Arthur–Clozel III.3.1 and III.4, printed pp. 201–202. The proof can use the
published `cyclicNormKernelCharacter`, `ideleClassNormTower`,
`ideleClassNormGaloisProduct`, and `ideleClassNormInclusionPower`.
