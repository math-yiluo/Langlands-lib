# The global Artin map for an infinite abelian extension

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K and an abelian Galois extension Ω/K, possibly infinite, this file builds a continuous global Artin homomorphism from the ideles of K to Gal(Ω/K). It is the limit of the finite global Artin maps `globalArtinMonoidHom` over the finite Galois subextensions. The first case is Ω = ℚ̃, the library's ZHat-extension of ℚ. The file also builds a positive archimedean section ℝ₊ˣ → I_ℚ that is killed by every finite abelian Artin map over ℚ and by the Artin map of ℚ̃. So every rational idele has the same Artin symbol in Gal(ℚ̃/ℚ) as some idele of norm one.

## Main definitions and results

- `infiniteGlobalArtinToLimit` and `infiniteGlobalArtinMonoidHom K Ω : IdeleGroup K →ₜ* Gal(Ω/K)`. The first lands in Mathlib's inverse limit over `FiniteGaloisIntermediateField K Ω`. The second moves this to the Krull-topological group by `InfiniteGalois.continuousMulEquivToLimit`.
- `restrictNormalHom_infiniteGlobalArtinMonoidHom` (simp): restricting to a finite Galois layer E gives the finite Artin map of E/K. Variants take E as an intermediate field, with explicitly supplied `NumberField` or `IsAbelianGalois` structures, or postcomposed with a map. `..._of_scalarTower` covers a finite abelian E/K embedded in Ω by any scalar tower.
- `infiniteGlobalArtinMonoidHom_denseRange`: the image is dense in the Krull topology.
- `rationalCyclotomicZHatGlobalArtin`: the case K = ℚ, Ω = ℚ̃, with its projection lemmas and dense range.
- `rationalPositiveArchimedeanIdele`: the idele with trivial finite part and the given positive real at the real place. Its absolute norm is r⁻¹ (`..._absoluteNorm`), and every finite abelian Artin map over ℚ kills it.
- `exists_normOneIdele_same_rationalCyclotomicZHatGlobalArtin` and `rationalCyclotomicZHatGlobalArtin_normOne_denseRange`: norm-one rational ideles already have dense image in Gal(ℚ̃/ℚ).
- Packaging helpers: `globalArtinMonoidHomOfNumberField`, with its norm-restriction naturality, and several `comp...Data...` subtypes that bundle values with their equalities.

## Proofs

The limit point is compatible because the finite Artin maps commute with restriction in towers (`globalArtinMonoidHom_restrict_tower`). Continuity holds coordinatewise. Density uses that a Krull neighbourhood of 1 contains the fixing subgroup of a finite layer, together with surjectivity of the finite Artin map (`globalArtinMonoidHom_surjective`). The archimedean section is killed because the local Artin map at a real place is trivial on positive reals.

## Points to watch

- Density of the image is proved, not surjectivity.
- The absolute idele norm follows the convention of `IdeleGroup.absoluteNorm`, under which the section of r has norm r⁻¹.
- ℚ̃ is the library's own construction, not a Mathlib field.
- Many declarations exist only to pass number-field witnesses explicitly. They state the same projection fact.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/InfiniteGlobalArtin.lean`: the Lean file is the source byte for byte (SHA-256 `aae107ed80c8c041fac2a7c7696f062072f32bf48a8c861678b3fb3032057414`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
