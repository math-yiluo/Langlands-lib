# Transport of the Artin map along field isomorphisms

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseSemilinearNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file shows that the universe-polymorphic abelian local Artin map `LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom` is compatible with isomorphisms of the data: an isomorphism of extensions over a fixed base, and a pair of ring isomorphisms K ≃ K', L ≃ L' compatible with the algebra maps (a semilinear isomorphism). All fields may live in different universes.

## Main results

- `abelianLocalArtinMonoidHom_autCongr`: for finite abelian extensions L and M of a nonarchimedean local field K and a K-algebra isomorphism e : L ≃ M, conjugating the Artin map of L/K by e gives the Artin map of M/K.
- `abelianLocalArtinMonoidHom_semilinear_conjugation`: let K, K' be nonarchimedean local fields, L/K and L'/K' finite abelian, eK : K ≃+* K' and eL : L ≃+* L' with eL ∘ `algebraMap` = `algebraMap` ∘ eK, and `hExt : SemilinearValuationCompatible K K' eK` (the valuation of K' pulled back along eK is equivalent to that of K). Then conjugation by `semilinearGaloisGroupCongr` carries the Artin image of a to the Artin image of eK(a).
- `abelianLocalArtinMonoidHom_semilinear_conjugation_apply` (pointwise form), `abelianLocalArtinMonoidHom_eq_one_of_semilinear` (if the image of eK(u) is trivial, so is that of u) and `abelianLocalArtinMonoidHom_semilinear_action`: eL applied to the Artin image of u acting on z equals the Artin image of eK(u) acting on eL(z).

## Proof

K' is made a degree-one extension of K through eK. The norm-restriction square of the naturality file is applied to it: the norm from K' to K undoes eK, and restriction from L' to L is inverse conjugation.

## Caveats

- The valuation compatibility `hExt` is an explicit hypothesis; the docstring stresses that it is a valued-field condition, not the Artin equality in disguise.
- `abelianLocalArtinMonoidHom_semilinear_action` has the same name as a theorem in the root namespace `LocalClassFieldTheory` about the `Type`-level map; only the namespace `Universe` distinguishes them.
- The pointwise forms are stated separately, per their docstrings, so that users need not unfold the monoid-hom equality.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseSemilinearNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `3f4adb012aa4e0bd1533a34d7ef272afa02b48c6411c57a26fff47a90dd8f23c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
