# Upper ramification groups under an isomorphism of base fields

Module `Nyll.ValuedFieldTheory.Ramification.LocalField.BaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A field E may be an algebra over two fields B and K whose images in E are identified by a ring isomorphism e : B ≃ K, compatible with the two maps into E. The file shows that when B and K are nonarchimedean local fields, E is finite Galois over both and e preserves the valuation rings, the upper ramification filtrations of E/B and E/K agree, once the two Galois groups are identified by their common action on E.

## Results

- `galoisGroupEquivOfBaseRingEquiv B K E e he`: the isomorphism Gal(E/B) ≅ Gal(E/K) that keeps the underlying automorphism of E. `galoisGroupEquivOfBaseRingEquiv_apply` records that it does not change the action on E.
- `localUpperRamificationGroup_map_baseRingEquiv`: let B and K be nonarchimedean local fields, each with a valuative relation, a topology and `IsNonarchimedeanLocalField`, let E be finite and Galois over both, and suppose e preserves the valuation rings: v_B(b) ≤ 1 exactly when v_K(e(b)) ≤ 1. Then for every real t, the isomorphism maps the upper group `localUpperRamificationGroup B E t` onto `localUpperRamificationGroup K E t`.

## Proof

The complete discrete valuations that the library chooses on E over B and over K have the same valuation ring, by unique extension. An earlier result shows that upper groups depend only on that ring, so one valuation on E can be used for both base fields. A private lemma then concludes: corresponding automorphisms move each integral element by the same amount, so the lower groups correspond. Their orders agree, hence the Herbrand functions and their inverses agree, and so do the upper groups.

## Watch for

- `localUpperRamificationGroup` is the library's own upper filtration, built from the valuation it chooses on E.
- The compatibility of e with the valuations is assumed only in the form of the valuation-ring condition `hvaluation`. Finite dimension and the Galois property are assumed separately over B and over K.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/LocalField/BaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `aa01b1345846e4621f549a45bac2450d5f26b3586c2866b47e26fc2e4a99277c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
