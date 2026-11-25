# Duality with values in the n-th roots of unity

Module `Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file collects the finite duality needed for the Kummer correspondence: characters of a finite abelian group `G` killed by `n` can be taken with values in `μ_n`, they separate points, and therefore the transpose of a character isomorphism `R ≅ Hom(G, μ_n)` is an isomorphism `G ≅ Hom(R, μ_n)`.

## Main definitions and results

Throughout, `K` is a field, `L` is a field over `K`, and `nthRootsSubgroup F n` is the library's subgroup of `n`-th roots of unity in `Fˣ`. The separation results, `nthRootsSubgroupEquivOfPrimitiveRoots`, the duality statement and the bijectivity of the transpose assume that `K` contains a primitive `n`-th root of unity (`hmu`); the other declarations do not.

- `characterToNthRoots`, `unitCharactersEquivNthRoots`: for `G` killed by `n`, a character `G → Kˣ` lands in `μ_n(K)`, giving `Hom(G, Kˣ) ≃* Hom(G, μ_n(K))`.
- `exists_nthRoots_character_apply_ne_one` and its version `..._in_extension` for `μ_n(L)`: for finite commutative `G` killed by `n` and `g ≠ 1`, some character `χ` with values in `μ_n` has `χ(g) ≠ 1`.
- `nthRootsSubgroupMap` (injective), `nthRootsSubgroupEquivRootsOfUnity` (agreement with Mathlib's `rootsOfUnity`), a `Fintype` instance, and `nthRootsSubgroupEquivOfPrimitiveRoots`: `μ_n(K) ≃* μ_n(L)`.
- `finiteNthRootsCharacterDuality`: there exists an isomorphism `Hom(G, μ_n(L)) ≃* G` for finite commutative `G` killed by `n`.
- `transposeCharacterEquiv e`: from `e : R ≃* Hom(G, M)`, the evaluation map `G → Hom(R, M)`, `g ↦ (r ↦ e r g)`.
- `transposeCharacterEquiv_injective`, `transposeCharacterEquiv_surjective`, `transposeCharacterMulEquiv`: for `G` finite commutative killed by `n` and `e : R ≃* Hom(G, μ_n(L))`, the transpose is an isomorphism `G ≃* Hom(R, μ_n(L))`.

## Proof

Separation comes from Mathlib's result for finite commutative groups over a field with enough roots of unity. Injectivity of the transpose is separation; surjectivity follows by counting, since both sides have the cardinality of `G` by the duality statement.

## Points to watch

- `finiteNthRootsCharacterDuality` only asserts that some (non-canonical) isomorphism exists; the transpose isomorphism is canonical.
- No correspondence between radical subgroups and extensions is asserted here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/FiniteDualSeparation.lean`: the Lean file is the source byte for byte (SHA-256 `b0de3164321a7cb416e6c30bb53709eba8ccf8e636fcbeb9df7b0a311f053671`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
