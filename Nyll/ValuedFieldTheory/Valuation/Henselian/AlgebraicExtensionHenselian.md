# Algebraic extensions of Henselian valuation rings are Henselian

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionHenselian`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `V` be a valuation subring of a field `K` that is Henselian along its maximal ideal, `L/K` an algebraic extension, and `W` a valuation subring of `L` whose valuation extends that of `V`.

`henselianRing_of_algebraic_extension`: `W` is Henselian along its maximal ideal. No assumption is made on rank, discreteness, completeness or separability.

The proof shows that `W` extends uniquely to every algebraic extension `M` of `L`: Chevalley's extension theorem gives an extension, and any two extensions of `W` are extensions of `V` to the algebraic extension `M/K`, so they have the same valuation ring by uniqueness over the Henselian base `V`. A criterion proved in an imported file turns unique extension to algebraic extensions into lifting of monic coprime factorizations over the residue field, and that into Henselianity of `W`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/AlgebraicExtensionHenselian.lean`: the Lean file is the source byte for byte (SHA-256 `b22da0831af70c85bc6ea913f0a57b699a73990a7d28915222519318070a668b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
