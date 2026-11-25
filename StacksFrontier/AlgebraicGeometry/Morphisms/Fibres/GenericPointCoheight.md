# Coheight of a fibre generic point

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointCoheight`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Under a flat morphism of locally Noetherian schemes, a generic point of a fibre component has the same coheight as its image in the base.

`AlgebraicGeometry.coheight_eq_coheight_base_of_asFiber_mem_genericPoints` states the equality for a point x of the source whose corresponding point `f.asFiber x` is generic in a component. `coheight_fiberι_eq_coheight_of_mem_genericPoints` states it for a point already given in a fibre. The flat local dimension formula adds the dimension of the fibre stalk to the dimension of the base stalk, and the fibre stalk has dimension zero at such a generic point. The coheight in these statements is the dimension of the ambient stalk.

`coheight_fiberι_eq_one_of_isDedekindDomain` applies to a flat, locally finite type morphism to a Dedekind spectrum and a fibre over a nonzero prime. The equality with base coheight and `Ideal.height_eq_one_of_isDedekindDomain` give coheight one.

Stacks Project, Tag 00ON and Tag 02JS.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/GenericPointCoheight.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
