# Artin maps at infinite places

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a Galois extension of number fields, v an infinite place of K and w a place of L above it. This file defines the local Artin map K_v^× → Gal(L/K). It is trivial if w is unramified over K. If w is ramified (v real, w complex), it sends x to 1 or to complex conjugation at w, according to the sign of x in K_v ≅ ℝ. The product of these maps over all infinite places gives an archimedean part of the global Artin map.

## Definitions

- `ramifiedInfinitePlaceConjugation w`: a chosen element of Gal(L/K) that induces complex conjugation at the ramified place w. It has order dividing 2.
- `infinitePlaceArtinMonoidHomOfPlace v w hw`: the map above, for a given place w over v.
- `chosenInfinitePlaceArtinMonoidHom v`: the same map for the place `chosenInfinitePlaceAbove v`, chosen by the local-block part of the library.
- `infinitePlaceGlobalArtinMonoidHom`: for L/K abelian, the product over the infinite places v of K of the local maps applied to the v-component of an idele.

## Main results

- `chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified`: at a ramified place the symbol of −1 induces complex conjugation along the chosen place.
- `chosenInfinitePlaceArtinMonoidHom_ker`: the kernel is `infiniteTensorNormSubgroup v`, the norms from the completions of L at v. When w is unramified this group is everything. When w is ramified it is the positive reals, the norms from ℂ to ℝ.
- `chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos`, `chosenInfinitePlaceArtinMonoidHom_continuous`.
- For L/K abelian: the map does not depend on the place above v (`infinitePlaceArtinMonoidHomOfPlace_eq`). It commutes with restriction to a subextension E (`chosenInfinitePlaceArtinMonoidHom_restrict_tower`). In a diamond K ⊆ K', L ⊆ L' with L'/K' abelian, the Artin map of L'/K' followed by restriction to L equals the Artin map of L/K applied to the local norm from K'_W to K_v (`chosenInfinitePlaceArtinMonoidHom_norm_restriction`).
- `infinitePlaceGlobalArtinMonoidHom_continuous`, `..._norm_restriction` (the archimedean half of norm-restriction compatibility, in the same diamond), and `..._finitePlaceIdele` (trivial on ideles supported at a finite place).
- Helpers: norms from a complex completion to a real one are positive; the norm between two real completions is the identity.

## Proofs

Independence of the place and compatibility with towers hold because the conjugation at a ramified place is the unique nontrivial element of Gal(L/K) that stabilizes that place and acts there as conjugation. The norm-restriction statements compare signs with the two norm lemmas.

## Points to watch

- The local map is the library's explicit sign-to-conjugation map, not obtained from a local class formation.
- `chosenInfinitePlaceArtinMonoidHom` and `infinitePlaceGlobalArtinMonoidHom` use one chosen place above each v. Independence of that choice is proved only for abelian L/K.
- The global product needs L/K abelian; the kernel, continuity and positivity results need only L/K Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/InfinitePlaceArtin.lean`: the Lean file is the source byte for byte (SHA-256 `727d8500d622ad515231f1c2c3cc25bdf35da11868dae9e154bbd3b7e882ec55`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
