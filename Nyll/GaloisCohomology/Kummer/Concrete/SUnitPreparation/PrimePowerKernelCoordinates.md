# Coordinates on kernels over ZMod (p^v)

Module `Nyll.GaloisCohomology.Kummer.Concrete.SUnitPreparation.PrimePowerKernelCoordinates`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file collects linear algebra over the rings `ZMod n` used in a finite S-unit preparation argument of Kummer theory: a surjection between finite free `ZMod (p^v)`-modules has a free kernel, and such a kernel, seen multiplicatively, is a product of copies of `ZMod (p^v)`, with the number of factors read off from its order.

## Main results

- `zmodPrimePower_isLocalRing`: for a prime `p` and `v > 0`, `ZMod (p^v)` is a local ring.
- `free_ker_of_surjective_linearMap_of_isLocalRing`: over a local commutative ring, the kernel of a surjective linear map between free modules, the source being finite as a set, is free. The proof splits the surjection by projectivity, so the kernel is a direct summand, hence finite projective, hence free.
- `card_eq_card_pow_card_chooseBasisIndex`: a free module `M` over a semiring `R`, with `R` and `M` both finite as sets, has `|R|^k` elements, where `k` is the size of a chosen basis.
- `exists_kernelMulEquiv_pi_zmod_of_primePower`: let `n = p^v`, and let `f : G →* H` be a surjection of commutative groups, `G` finite, whose additive versions are free `ZMod n`-modules. If the kernel has `n^q` elements, it is isomorphic to `(ZMod n)^q` (written multiplicatively).
- `galois_pow_eq_one_of_equiv_pi_zmod`: if the Galois group of an intermediate field `E` is isomorphic to `(ZMod n)^r`, every automorphism has `n`-th power `1`.

## Helper constructions

`additiveZModModuleOfPowEqOne` gives the `ZMod n`-module structure on the additive form of a commutative group of exponent dividing `n`; `additiveCoordinatesLinearEquiv`, `additivePiLinearEquiv` and `monoidKerEquivMultiplicativeLinearKer` turn multiplicative isomorphisms and kernels into `ZMod n`-linear ones.

## Points to watch

- The modules are multiplicative groups passed through `Additive`, and the `ZMod n`-module structures and freeness are hypotheses (instance arguments and `freeG`, `freeH`), not derived.
- The kernel coordinates are an existence statement (`Nonempty`), not a canonical isomorphism.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/SUnitPreparation/PrimePowerKernelCoordinates.lean`: the Lean file is the source byte for byte (SHA-256 `d5d1e5b68796556c65e63c81decfb4e45227f916e809509f985032cc2a659ef1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
