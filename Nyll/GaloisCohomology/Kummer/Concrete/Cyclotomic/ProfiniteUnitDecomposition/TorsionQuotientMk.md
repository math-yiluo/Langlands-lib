# Evaluating the torsion-quotient isomorphism

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

- `torsionQuotientEquivOfZHatMulDecomposition_mk` (simp lemma): for a compact commutative topological group `G`, a decomposition `E : G ≃ₜ* ℤ̂ × T` with dense torsion in `T`, and `g ∈ G`, the isomorphism `G ⧸ closure(torsion of G) ≃ₜ* ℤ̂` sends the class of `g` to the first coordinate of `E g`. It holds by definition.

It is the commuting square used to pass between a cyclotomic character and the `ℤ̂`-coordinate attached to the fixed field of its torsion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/TorsionQuotientMk.lean`: the Lean file is the source byte for byte (SHA-256 `f5e9ddd315c2d8f9cbe03f7455d17a33d0587fc8950bfab02aa0ab18a30f520d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
