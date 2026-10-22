# Actual virtual-representation and trace realization

This derived construction connects the parameter branch's genuine
finite-dimensional representation classes with the finite-representation
branch's concrete split Grothendieck group. The group and carrier universes
remain independent. The coefficient field is the actual complex field.
The group may be infinite; its topology is used only in the continuous
irreducible basis supplied by `Weil.Generic`.

`finiteClass` descends `FiniteRep.classOfRepresentation` through genuine
equivariant representation isomorphisms. That constructor transports a
finite-dimensional carrier to coordinates by a proved equivariant linear
equivalence. Its equality criterion proves `finiteClass_injective`; the
coordinate model therefore does not identify inequivalent representations.
No representative choice is made on the quotient without proving this
compatibility.

In the other direction, `liftFiniteRepresentation` transports an actual
coordinate representation to `ULift` in the specified carrier universe.
`liftFiniteEquiv` proves it equivariantly equivalent to the original.
This gives `finiteClass_surjective` and the genuine class-set equivalence
`finiteClassEquiv`. No universe resizing axiom or smallness assumption on the
group is used.

`basisFiniteClass` forgets the positive-rank label and continuous-irreducible
condition only after obtaining the underlying actual isomorphism class.
`realizeVirtual` extends its image in the split Grothendieck group by integral
linearity. Composing with the actual trace-character map gives `traceCharacter`.
`traceImage` and `realizeTrace` use its genuine image, and
`unitaryTraceCharacter` restricts it to the actual specified unitary basis.
No claim identifies the free irreducible lattice with either the split
Grothendieck group or its character image. In particular, no semisimplicity,
character faithfulness or irreducible decomposition is assumed.
The generator evaluation formulas are proved in the same module.

## Actual finite-group induced spans

For a finite group `H` and a supplied group homomorphism `f : G →* H`,
a monomial datum is an actual subgroup of `H` together with a unit-valued
one-dimensional character. `inflatedMonomial` applies the existing actual
subgroup induction, passes to the split virtual class, and restricts along `f`.
The coordinate and finite-dimensionality obligations for induction are already
proved in the imported finite-representation construction.

`inflatedMonomialSpan` is the integer span of these concrete virtual classes.
`monomialGenerator` and `evaluateMonomials` supply actual elements and evaluation
into that span, with the span-membership fields proved. Its image under trace
realization is `inflatedInducedCharacters`.
The two preimages `inducedVirtualPreimage` and `inducedTracePreimage` are
defined separately. No equality between them, no equality with a
factorization-supported sublattice, and no Brauer spanning conclusion is
built into a definition.

The map `f` is not silently assumed continuous or surjective. These algebraic
constructions do not claim that all inflated objects belong to the continuous
irreducible basis. Actual local finite Galois quotient maps, their topology,
irreducible decomposition, and the later passage into the local irreducible
lattice remain further obligations.

## Provenance and published dependencies

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), sections 2.5–2.6, printed pp.445–447, defines the free
irreducible lattice and its linear extensions. Section 3.1, p.448, and section
3.7, p.451, use actual finite Galois quotient representations and actual induced
rank-one classes. Those original passages were read. This file is an internal
bridge between the concrete Lean models needed there; it proves or assumes
none of the spanning or correspondence conclusions.

- Literature ID: `henniart-2000-simple-proof`.
- Source SHA256:
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

This construction imports published modules by their Lean names. At Library
commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`, the relevant module pairs are:

- `Langlands/VirtualRepresentation/Integral.{lean,md}` and
  `Langlands/VirtualRepresentation/Weil/Generic.{lean,md}`.
- `Langlands/Weil/Representation/Basic.{lean,md}` and
  `Langlands/Weil/Representation/Predicates.{lean,md}`.
- `Langlands/Representation/Finite/Classes.{lean,md}`,
  `Langlands/Representation/Finite/Induction.{lean,md}`, and
  `Langlands/Representation/Finite/Virtual.{lean,md}`.

The finite-representation modules supply actual coordinate representation
classes, subgroup induction and the split Grothendieck group. They are imported
without modification. The present bridge and its intrinsic quotient proofs
are authored by Worker 24.

The prepared environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` pins Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation and independent semantic acceptance are separate checks.
