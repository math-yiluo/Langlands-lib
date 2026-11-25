# Restriction naturality of the local Artin map in finite abelian towers

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K` and a tower `K ⊂ E ⊂ L` with `E/K` and `L/K` finite abelian, this file proves that the finite local Artin maps commute with restriction `Gal(L/K) → Gal(E/K)`. The two extensions are placed compatibly in `SeparableClosure K` by choosing an embedding of `L` and restricting it to `E` (`towerLowerEmbedding`); the abstract norm-restriction naturality of the class formation then becomes actual Galois restriction.

## Main results

- `concreteNormResidueAutomorphism_restrict_tower`: for an embedding `iL : L →ₐ[K] SeparableClosure K`, degree data `D`, valuation data `v` and a class field axiom `hcf` on the absolute units, restricting the norm-residue automorphism of `a ∈ Kˣ` for `L` to `E` gives the one for `E` (with the restricted embedding).
- `localArtinAutomorphism_restrict_tower`: the pointwise statement for `localArtinMonoidHom`, with the canonical local data (`localResidueDatum`, `localHenselianValuation`, `separableClosureUnits_isClassFormation`).
- `abelianLocalArtinMonoidHom_restrict_tower`: restriction composed with `abelianLocalArtinMonoidHom K L` equals `abelianLocalArtinMonoidHom K E`.
- `restrictNormalHom_eq_autCongr`: for a `K`-isomorphism `e : L ≃ M` with `M/K` normal, restriction from `L` to `M` (with `L` an `M`-algebra through `e⁻¹`) is conjugation by `e`.
- `abelianLocalArtinMonoidHom_autCongr`: the finite abelian Artin maps are compatible with a `K`-isomorphism `L ≃ M`, the Galois groups being identified by conjugation.
- `ClassFieldTheory.finiteAbelianLocalArtinMap_restrict_tower`: the tower statement for `abelianLocalArtinMap`.

## Proofs

The first theorem applies the abstract norm-restriction naturality with trivial base extension, where the relative norm is the identity, and identifies abstract quotients with Galois groups compatibly with restriction. The local statements rewrite the Artin map through a chosen embedding into the separable closure.

## Points to watch

In `concreteNormResidueAutomorphism_restrict_tower` the class field axiom is the hypothesis `hcf : SatisfiesClassFieldAxiom (intrinsicAbsoluteUnits K)`, together with `D` and `v`; the local versions supply the canonical ones. All fields are in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `d878d844012c76f323216fec1f2bb4acfeb1381bf5232e3c62e783968e16a46f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
