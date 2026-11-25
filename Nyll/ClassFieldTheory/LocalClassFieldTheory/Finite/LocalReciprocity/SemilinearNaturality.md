# Semilinear naturality of the finite local Artin map

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` and `L'/K'` be finite abelian extensions of nonarchimedean local fields, and let `eK : K ≃ K'` and `eL : L ≃ L'` be ring isomorphisms with `eL` restricting to `eK`. This file proves that the local Artin maps correspond: conjugating the Artin symbol of `u ∈ Kˣ` by `eL` gives the Artin symbol of `eK u`.

## Main definitions

- `SemilinearValuationCompatible K K' eK`: the proposition that, with `K'` made a `K`-algebra through `eK`, the valuation of `K'` extends that of `K`; that is, `eK` matches the chosen valuations.
- `SemilinearBaseCompatible`: a structure recording that `eL` restricts to `eK` on the base.
- `semilinearGaloisGroupCongr`: the isomorphism `Gal(L/K) ≃* Gal(L'/K')`, `σ ↦ eL ∘ σ ∘ eL⁻¹`; `semilinearGaloisGroupCongr_apply_equiv` and `SemilinearBaseCompatible.conjugation_apply` evaluate it.

## Main results

- `abelianLocalArtinMonoidHom_semilinear_conjugation`: assuming `eL` restricts to `eK` and `SemilinearValuationCompatible K K' eK`, conjugation composed with `abelianLocalArtinMonoidHom K L` equals `abelianLocalArtinMonoidHom K' L'` composed with the map `Kˣ → K'ˣ` induced by `eK`.
- `abelianLocalArtinMonoidHom_semilinear_conjugation_apply` and `abelianLocalArtinMonoidHom_semilinear_action`: the same at one unit, and as the identity `eL (Art(u) z) = Art(eK u) (eL z)` for `z ∈ L`.
- `abelianLocalArtinMonoidHom_eq_one_of_semilinear`: if the symbol of `eK u` for `L'/K'` is trivial, so is the symbol of `u` for `L/K`.

## Proof

`K'` is viewed as an extension of `K` of degree one through `eK`; the norm-restriction naturality of the Artin map (`abelianLocalArtinMonoidHom_norm_restriction`, from another file) is applied to the square `K ⊂ K'`, `L ⊂ L'`. The norm from `K'` to `K` is then `eK⁻¹`, and restriction becomes inverse conjugation.

## Points to watch

The valuation compatibility is a hypothesis: a bare field isomorphism of local fields need not be assumed to respect the given valuative relations. The Artin map statements take `K`, `K'`, `L` and `L'` in `Type`; the compatibility definitions and `semilinearGaloisGroupCongr` are universe-polymorphic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SemilinearNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `d61bfd7f3d780f17a57daeadce861616abec5a4a27a17c87edea6c904a63a585`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
