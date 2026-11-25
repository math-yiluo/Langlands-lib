# Galois actions on fixed-field idele classes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionAction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file shows that the identifications of fixed parts of `rationalIdeleClassRepresentation` with idele class groups of actual fields respect Galois actions: the action of `Gal(ℚˢᵉᵖ/ℚ)` on the direct limit matches the action of field automorphisms on idele classes, and the quotient action on an abstract finite extension matches the Galois action on a relative idele class group.

## Main results

- `rationalIdeleClassEquivFixed_action_coe`: for a finite intermediate field `E`, `τ ∈ Aut(E/ℚ)` and any `σ ∈ Gal(ℚˢᵉᵖ/ℚ)` restricting to `τ` on `E`, acting by `σ` on the image of a relative idele class `c` gives the image of `τ • c`.
- `rationalIdeleClassEquivFixed_ambientAlgEquiv`: if `e : E ≃ F` between finite intermediate fields is induced by `σ`, then `σ` sends the image of `c ∈ C_E` to the image of `ideleClassCongr e c ∈ C_F`.
- `rationalAbstractExtensionIdeleClassEquiv_action`: for closed subgroups `L ≤ K` with `L` normal in `K`, `K` of finite index in the whole group and `L` of finite index in `K`, and with fixed fields `F ⊆ E`: for every `q ∈ K/L`, the equivalence `rationalAbstractExtensionIdeleClassEquiv` carries the action of `q` on the extension fixed representation to the action of the corresponding element of `Gal(E/F)` (given by `abstractExtensionQuotientEquivGaloisGroup`) on `RelativeIdeleGroup.ClassGroup F E`.

## Proofs

The first two results are the direct-limit statements of another file, read through `rationalIdeleClassEquivFixed`. For the third, one reduces to a coset representative `σ ∈ K`; the coset action is then `ρ(σ)`, `σ` restricts on `E` to the Galois element attached to `q`, and the base change to the tower `ℚ ⊆ F ⊆ E` is equivariant. Private lemmas handle the relative fixed field and the chain of four additive equivalences.

## Points to watch

- The comparison is stated pointwise, for each `q` and each element, not as an isomorphism of representations.
- On `RelativeIdeleGroup.ClassGroup F E` the action is `RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E`, and `F ⊆ E` is Galois through `abstractRelativeFixedField_isGalois`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitExtensionAction.lean`: the Lean file is the source byte for byte (SHA-256 `368d724dc47075c3d1bfbe70f050e2487ef5a1bc977814ea74be86f234ee2f54`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
