# Degree-p subextension of a cyclic p-power extension and splitting

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a cyclic Galois extension L/K of number fields whose group has order p^n with n > 0, this file takes the fixed field M of a normal subgroup of index p. M/K is then cyclic Galois of degree p. The file shows that a finite place of K splitting completely in L splits completely in M, and so a place not split in M is not split in L. Along the way it proves general facts on decomposition groups of absolute values.

## Decomposition groups of absolute values

For a field extension E/F, `absoluteValueDecompositionGroup F w` is the library's decomposition group of an absolute value w on E: the automorphisms σ with w(σx) < 1 ⇔ w(x) < 1 for all x.

- `restrictAbsoluteValueExtensionToIntermediate`: restricts an exact extension w of vF to an intermediate field M.
- `absoluteValueDecompositionGroup_map_restrictNormalHom`: for E/F Galois, F ⊆ M ⊆ E with M/F normal and vF nontrivial, restriction to M maps the decomposition group of w onto that of the restriction of w to M.
- `absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv`: equivalent absolute values have equal decomposition groups.
- `..._conjugate_eq_of_isMulCommutative`, `..._eq_of_exactExtensions_of_isMulCommutative`: when Gal(E/F) is abelian, conjugating an exact extension keeps its decomposition group; if also E/F is Galois and vF nontrivial, all exact extensions of vF share it.
- `absoluteValueDecompositionGroup_conjugate_eq_bot`, `..._eq_bot_independent_extension`: triviality of the decomposition group survives conjugation; for E/F Galois and vF nontrivial, it does not depend on the exact extension of vF.

## The degree-p subextension

Given `hp : p.Prime`, `0 < exponent` and |Gal(L/K)| = p^exponent:

- `cyclicPrimeIndexSubgroup`: a chosen normal subgroup of index p.
- `cyclicPrimeSubextension`: its fixed field M; it is Galois over K, `cyclicPrimeSubextension_finrank` gives [M : K] = p, and `cyclicPrimeSubextension_isCyclic` says Gal(M/K) is cyclic.
- `cyclicPrimeSubextensionDecompositionGroup v`: the image in Gal(M/K) of the decomposition group of v in L/K. `..._eq_quotient_image` matches it with the image in the quotient group transported by the Galois correspondence.

## Splitting

- `finitePlaceSplitsCompletely_in_cyclicPrimeSubextension`: if `FinitePlaceSplitsCompletely v` for L/K, the restricted decomposition group is trivial.
- `finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_actual`: then `FinitePlaceSplitsCompletely v` also holds for M/K.
- `finitePlace_not_splitsCompletely_of_not_in_cyclicPrimeSubextension` and `..._actual`: the contrapositives.

## Points to watch

- The decomposition group and `FinitePlaceSplitsCompletely` are the library's notions; complete splitting means the decomposition group of the library's chosen extension `chosenFinitePlaceExtension` is trivial.
- The group order must be a prime power p^exponent, not merely cyclic. The subgroup is made by choice.
- `cyclicPrimeSubextensionDecompositionGroup` is defined as an image under restriction, not as the decomposition group of the chosen extension of v to M. By `absoluteValueDecompositionGroup_map_restrictNormalHom` such an image is the decomposition group of the restricted absolute value; the `_actual` statement reaches the chosen extension to M for triviality only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/CyclicPrimeSubextension.lean`: the Lean file is the source byte for byte (SHA-256 `5db07478c6c74c7870f1c78a161cc3a7720f46499e01ba3449f6f1861ab564c1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
