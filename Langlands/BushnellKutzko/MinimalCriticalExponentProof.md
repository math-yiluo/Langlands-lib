# The critical exponent and minimality

`minimalCriticalExponent` proves `MinimalCriticalExponentStatement`, the
Library form of Bushnell–Kutzko (1993), Proposition (1.4.15), printed p. 41
(PDF p. 53). The source is `bushnell-kutzko-1993-admissible-dual-gln`.
The base field, vector space and extension field remain in independent
universes. The hypothesis that the generator is outside the base field
ensures that it is nonzero.

The critical-index theorem `adjointExactness` supplies a greatest
critical index. At the generator's shift the adjoint lattice is the full
order. Nonemptiness of the critical-index set makes that shift a critical
index. By antitonicity, the shift equals the maximum exactly when the
next adjoint lattice lies in the sum of the integral centralizer and
the first filtration step.

The proof of the containment criterion uses the successive quotients
of the given chain. On each quotient, the extra commutator depth means
intertwining the action of the generator across its shift. The uniformizer
of the base gives the periodicity condition. Under coprimality of the
normalized exponent and the ramification index, Bézout gives the shift
of an extension uniformizer. If the shift-zero combination generates the
extension residue field, the layer maps intertwine the extension's
integer units and then all extension field units. Lifting over the
extension integers produces an integral centralizer element whose
layer maps agree. Failure of coprimality gives an indicator family on
one class of indices. Failure of residue generation gives a projection
over a proper residue subfield transported along an orbit. The families
lift over the base and certify failure of the containment.
