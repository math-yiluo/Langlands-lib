# Ramification of local-field extensions: collecting module

Module `FontaineWintenberger.Ramification`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

This file contains no declarations. It imports all the modules of the ramification part of the library, so that `FontaineWintenberger.Ramification` gives access to them at once.

The imported modules are grouped under `FontaineWintenberger.Ramification` as follows:

- `Different`: the different (Hilbert's formula, monogenic extensions, subextensions, trace ideals);
- `Embedding`: ramification data for embeddings, in general and for valued fields;
- `Fields`: inertia, tame and wild subfields, non-normal extensions, towers of prime degree;
- `Herbrand`: Herbrand functions, their affine pieces, inverses, intervals and behaviour under subgroups;
- `Infinite`: ramification for infinite extensions, restrictions, limits, scalar towers and splitting fields;
- `Lower`: lower ramification groups and their properties (base change, degree, fixed fields, generators, index, inertia, tame and wild parts, towers, uniformizers, Teichmüller and residue digits, and others);
- `Norm`: norm estimates (approximation, congruence, towers, valuation);
- `Upper`: upper ramification groups (base change, quotients, order, fixed fields, local constancy, transport, and others).

The file's comment says the material follows Serre's *Local Fields*.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification.lean` (SHA-256 of the source file `92622d74067b39937f37b1599786f312d7d37bd122313e717971cb486e04248f`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
