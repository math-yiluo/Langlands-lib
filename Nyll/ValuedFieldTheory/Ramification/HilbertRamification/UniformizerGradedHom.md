# The uniformizer homomorphism G_n/G_(n+1) → U^n/U^(n+1)

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.UniformizerGradedHom`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`. Write O_L for the valuation ring of L, m_L for its maximal ideal, and G_n for the lower ramification groups. Fix a uniformizer π of L. The file constructs, without completeness, the homomorphism σ ↦ σ(π)/π from G_n/G_(n+1) to U^n/U^(n+1). It shows that the map does not depend on π, and that it is injective when the residue extension is separable.

## Definitions

- `dvfHigherPrincipalUnitGroup target n`: the units a of O_L with a − 1 ∈ m_Lⁿ. For n = 0 this is the whole unit group. The groups decrease with n.
- `dvfPrincipalUnitGradedPiece target n` and `lowerRamificationGradedPiece huniq n`: the quotients U^n/U^(n+1) and G_n/G_(n+1).
- `dvfUniformizerQuotientUnit huniq π hπ σ`: a chosen unit u with σ(π) = u·π.
- `uniformizerGradedHom huniq π hπ n`: the induced homomorphism G_n/G_(n+1) → U^n/U^(n+1), obtained from the representative map `dvfUniformizerRepresentativeHom`.
- `valuationSubringAlgEquivOfUniqueExtension`: the action of σ on O_L, as an automorphism of O_K-algebras.

## Results

- The units u(σ) satisfy u(στ) = σ(u(τ))·u(σ), and u(σ) ∈ U^n exactly when σ(π) − π ∈ m_L^(n+1).
- If σ ∈ G_n, then u(σ) ∈ U^n, and σ(a)/a ∈ U^(n+1) for every unit a.
- An exact formula relates u(σ) for two uniformizers that differ by a unit.
- `uniformizerGradedHom_eq_of_uniformizers`: the homomorphism does not depend on π. `uniformizerGradedHom_mk_eq_one_iff` describes its kernel.
- `polynomial_argument_sub_mem_succ_dvf`: if P′(a) is a unit, b − a ∈ m_L^(n+1) and P(b) − P(a) ∈ m_L^(n+2), then b − a ∈ m_L^(n+2).
- `uniformizerGradedHom_injective_of_residue_isSeparable`: if the residue extension is separable, the homomorphism is injective.

## Proof of injectivity

The monogeneity theorem gives a generator x of O_L over O_K and a polynomial P over O_K with P(x) a uniformizer and P′(x) a unit. Since the homomorphism does not depend on π, one may take π = P(x). If σ(π)/π ∈ U^(n+1), then P(σx) − P(x) ∈ m_L^(n+2). The Taylor step gives σx − x ∈ m_L^(n+2), and since x generates O_L, σ lies in G_(n+1).

## Watch for

- Unique extension of the valuation is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target`.
- Injectivity assumes the residue extension separable. The file's comment says that without this hypothesis injectivity fails for fiercely ramified extensions.
- The target is the quotient U^n/U^(n+1) itself. The file does not identify it with the multiplicative or additive group of the residue field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/UniformizerGradedHom.lean`: the Lean file is the source byte for byte (SHA-256 `cd1b046c04754d477c784f38c05cb738ef670e5a8c49601c12ca7534414f4737`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
