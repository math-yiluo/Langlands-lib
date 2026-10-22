# Induction on Tate classes

Original proof: Worker 45. Audit and documentation: Worker 25.

This helper proves an induction principle for properties of classes in Mathlib's
actual Tate cohomology. One supplies a degree-zero proof, preservation when
lifting along the embedding shift, and reflection along the augmentation shift.
The positive induction uses the proved surjectivity of the embedding connecting
isomorphism. The negative induction normalizes integer degrees explicitly.

The shift isomorphisms and scalar-split sequences are the constructions in
`ShiftDefinitions`. This is a proof principle used to establish further laws,
not an assumed law of any cohomology operation. It implements the
dimension-shifting method of Serre, *Local Fields* (1979), VIII §1,
printed pages 128–129 (PDF pages 134–135); source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
