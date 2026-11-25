# Transporting Galois extensions along ring isomorphisms

Module `Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given field extensions L/K and N/M and ring isomorphisms f : K ≃ M and g : L ≃ N compatible with the two algebra maps (`hcomp`: g ∘ (K → L) = (M → N) ∘ f), this file transports Galois-theoretic structure from L/K to N/M. Only Mathlib's Galois theory is used.

- `isAbelianGalois_of_equiv_equiv`: if L/K is abelian Galois (`IsAbelianGalois K L`), so is N/M. Galois-ness comes from Mathlib's `IsGalois.of_equiv_equiv`; commutativity from the injective multiplicative map Gal(N/M) → Gal(L/K), σ ↦ g⁻¹ ∘ σ ∘ g.
- `galEquiv_of_equiv_equiv`: the bijection Gal(N/M) ≃ Gal(L/K) given by the same conjugation, with inverse τ ↦ g ∘ τ ∘ g⁻¹.

`galEquiv_of_equiv_equiv` is stated as an equivalence of types only; the file does not record that it is a group isomorphism, although the proof of the first result checks that the forward map is multiplicative.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Algebra/AbelianGaloisEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `231022aa2740427842ff657fdaa530c97c4b29f29f1ab639522cbe8d6e8d41f4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
