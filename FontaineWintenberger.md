# The field of norms of Fontaine and Wintenberger: root of the library

Module `FontaineWintenberger`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

This file declares nothing. It imports the five parts of the library (`APF`, `FieldOfNorms`, `LocalField`, `Mathlib`, `Ramification`), and its comment lists the main statements, for a complete discretely valued field `K` with perfect residue field (`IsPerfectResidueLocalField K`) and a separable extension `L/K`:

- arithmetically profinite and strictly arithmetically profinite extensions: `IsAPF K L`, `isAPF_iff_isOpen_apfSubgroup`, `IsStrictlyAPF K L`, `isStrictlyAPF_iff`;
- the field of norms `FieldOfNorms K L` of norm-compatible families, a complete discretely valued field of characteristic `residueChar K` with residue field isomorphic to that of `L` (`FieldOfNorms.residueEquiv`);
- `FieldOfNorms.algHomEquiv` and the isomorphism of absolute Galois groups `FieldOfNorms.absoluteGaloisEquiv`;
- the Galois action `FieldOfNorms.aut`, `RelFieldOfNorms.ambientGaloisEquiv`;
- the tower of elementary extensions (`apfElementaryStage`, `apfElementaryLevel`) and its characterization of APF;
- the comparison of upper ramification groups `RelFieldOfNorms.map_normUpperRamificationGroup`.

By the comment, the field-of-norms statements assume `L/K` infinite and APF; the ambient Galois action also assumes `L/K` Galois.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, 1.2.1, 1.4.1, 1.4.2, 2.1.1, 2.1.3, 3.2.2 (ii), 3.2.3, 3.2.4, 3.3.6.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger.lean` (SHA-256 of the source file `a12eba0f7c410d1fca559d496ed6b74fd6615d0d52a2cd6b8f0bbc5c3ec8598d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
