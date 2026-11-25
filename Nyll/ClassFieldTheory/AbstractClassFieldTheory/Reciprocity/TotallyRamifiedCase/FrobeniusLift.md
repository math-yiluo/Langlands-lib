# Degree-one Frobenius lifts in totally ramified extensions

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FrobeniusLift`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory with degree map `D`, for `K : FiniteResidueAbstractField D`, a Frobenius element of L/K is a class of the subgroup of K modulo the inertia attached to L inside it (`D.extensionInertiaWithin K.field L.field L.below`) whose normalized degree is a positive integer, its exponent. This file shows that in a totally ramified Galois extension every automorphism lifts to a Frobenius element of exponent one, and builds from it the auxiliary finite Galois extension M used in the totally ramified reciprocity argument.

## Definitions and results

- `exists_degreeOneFrobeniusLiftOfTotallyRamified`: if L/K is Galois and totally ramified (`hTot`), each q ∈ G(L/K) is the restriction of some σ in `D.FrobeniusElements K L` with `frobeniusExponent` 1. The proof multiplies the chosen degree-one Frobenius element by an element of trivial degree in the class of q·(its restriction)⁻¹, using total ramification to adjust the degree.
- `chosenDegreeOneFrobeniusLiftOfTotallyRamified`, and its version `chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified` for finite Galois extensions: a choice of such a lift (written σ̃ below), with simp lemmas for its exponent and restriction.
- `abstractReciprocityTotallyRamifiedFiniteGaloisExtension`: for L/K finite Galois totally ramified and q ∈ G(L/K), a finite Galois extension M of K (`galoisRefinement`) refining the compositum of L and the fixed field Σ of σ̃. Requires `G` compact and Hausdorff.
- The three comparison lemmas say that M contains L (`…_le_L`) and Σ (`…_le_sigma`), and is contained in the maximal unramified extension of L (`maximalUnramifiedField_le_…`).

## Points to watch

- Lean statements are in subgroup order: `M.field.toSubgroup ≤ L.field.toSubgroup` means M ⊇ L as fields.
- The lift is picked by `Classical.choose`; later results use this particular choice.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean`: the Lean file is the source byte for byte (SHA-256 `ebfae75701c9fbdd89bca7acde78e75779be9dbfc23ca649d310e164feb4d912`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
