# Surjectivity of the infinite global Artin map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinSurjectivity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field and Ω/K an abelian Galois extension, possibly infinite. This file proves that the global Artin map, from the ideles of K and from the idele class group C_K to Gal(Ω/K), is surjective. The previous files gave only a dense image.

## Main results

- `infiniteGlobalArtinMonoidHom_positiveArchimedeanSection` (simp): the Artin map kills the positive archimedean section `IdeleGroup.positiveArchimedeanSection K`. This section sends a positive real r to an idele with trivial finite components and positive infinite components.
- `exists_normOneIdele_same_infiniteGlobalArtin`: every idele has the same Artin symbol as some idele of absolute norm 1.
- `infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective`: the continuous Artin map C_K → Gal(Ω/K) is surjective.
- `infiniteGlobalArtinMonoidHom_surjective`: the Artin map I_K → Gal(Ω/K) is surjective.
- `numberFieldPositiveArchimedeanIdele` and its lemmas (finite components trivial, infinite components positive, absolute norm r⁻¹) are alternative names for the section and its properties.

## Proof

A positive component at an infinite place lies in the local norm subgroup, so every finite Artin map kills the section. Hence the infinite map, which is the limit of the finite ones, kills it too. Multiplying an idele by the section of its absolute norm gives an idele of norm one with the same symbol (`IdeleGroup.positiveArchimedeanNormOneCorrection`). So norm-one idele classes already have dense image. Their group is compact (from the imported `NormOneCompact`), so the image is also closed, hence everything.

## Points to watch

- The absolute idele norm follows the convention of `IdeleGroup.absoluteNorm`, under which the section of r has norm r⁻¹.
- Surjectivity rests on the dense-range result of the earlier files. That result uses surjectivity of the finite global Artin maps, which is not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/InfiniteGlobalArtinSurjectivity.lean`: the Lean file is the source byte for byte (SHA-256 `b1eeebb4b54a0cf26845feacdf33f1d6cefa2d1a4d313f77a61be5863bccff09`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
