# Smoothness and fibre generic points under isomorphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.SmoothAtIso`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A commuting square with source isomorphism e : X ≅ X′ and base isomorphism σ : S ≅ S′ transports smoothness and generic points of fibre components.

Assume f and f′ are locally of finite presentation. Then `Scheme.Hom.smoothLocus_eq_preimage_of_iso` identifies the smooth locus of f with the inverse image under e of that of f′, and `InfinitesimalLifting.smoothAt_iso_hom_iff` equates smoothness at x with smoothness at e(x). The square is cartesian, and the base isomorphism supplies flatness for the smooth-locus comparison.

`mem_genericPoints_asFiber_iso_hom_iff` equates being generic in an irreducible component of the fibre of x with the corresponding property at e(x). This works for arbitrary morphisms in such a square. The proof transports generalizations within the fibre using the source isomorphism and injectivity of the base isomorphism.

Stacks Project, Tag 09IL and Tag 02V4.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/SmoothAtIso.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
