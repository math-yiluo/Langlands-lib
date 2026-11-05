# Affine generic geometric irreducibility spreading

Workers 336 and 1606. This proves the published proposition
`Langlands.Algebra.FiniteTypeGeometricIrreducibilitySpreading` with its three
independent universes and its actual generic residue-field tensor.
It is the internal affine algebraic reformulation of Stacks Project
Lemma 37.27.5 (0559), registered as
`stacks-generic-geometric-irreducibility-2026-11-04`.

For a faithful finite type domain algebra C over a domain R, take any fraction
field F of R and its algebraic closure Ω. Give Ω its canonical algebra structure
over Frac(R), using its faithful R action. Worker 1606's fraction-tensor
comparison transfers the prime nilradical of Ω tensor_R C to that of
Ω tensor_Frac(R) Frac(C). Worker 336's extraction of separable constants then
shows that Frac(R) is separably closed in Frac(C). The domain spreading core
produces one nonzero element of R that works for every field specialization.

Worker 1606's nilradical reductions remove the domain and faithfulness
conditions: first quotient an arbitrary algebra by the contracted geometric
generic nilradical, using uniform specialization of generic nilpotence to
recover nearby tensors; then quotient the base by its prime nilradical.
Its actual generic residue field is a fraction field of this reduced base.
Tensor cancellation transports both the generic premise and every nearby field
conclusion. A representative of the resulting nonzero base element is
non-nilpotent in the original base.

The conclusion uses all field maps in the independent test-field universe.
No Noetherian, flatness, finite-presentation, perfect-field or ground-field
finite-type premise is added. The scheme comparison is supplied separately by
the algebraic-geometry proof modules.
