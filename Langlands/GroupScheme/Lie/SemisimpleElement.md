# Geometric semisimplicity of actual Lie elements

`IsGeometricallySemisimpleMatrix M` tests the endomorphism given by `M` after
entrywise extension to the algebraic closure of its field. In particular, over
an imperfect field this definition does not confuse a squarefree inseparable
minimal polynomial with geometric semisimplicity.

`Lie.IsSemisimpleElement G X` requires this property for the differential of
every finite dimensional algebraic group representation of the actual group
scheme `G`, written in coordinates as `G → GL_(Fin n)`. The differential is the
actual dual-number tangent matrix, rather than a supplied abstract action.
The zero tangent vector is semisimple, epsilon scaling preserves the property,
and actual group-scheme homomorphisms preserve it by restricting each target
representation. These claims require no smoothness or connectedness assumption.

The provenance is a derived algebraic-representation convention for the
semisimple Lie elements used in Milne, *Algebraic Groups* (2017), Proposition
17.74, Example 17.75 and the paragraph before Proposition 17.76, printed p.377
/ PDF p.393. That paragraph says representations of the Lie algebra; the present
predicate explicitly tests differentials of algebraic group representations.
This file does not assert equivalence with a predicate testing arbitrary
abstract Lie-algebra representations, nor a reduction to one faithful
representation. The geometric matrix condition is explicit in the definition.
No Jordan decomposition, stabilizer smoothness, or existence of noncentral
semisimple elements is asserted here.
