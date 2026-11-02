# Tensor pushouts over a specified base algebra

Author: Worker 105.

This is derived algebraic infrastructure for the fibre-product axiom in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1, printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For compatible towers of commutative algebras R → C → A,B,
`affineTensorPushout` constructs the cocone in `CommAlgCat R` with vertex
A ⊗[C] B and the two usual inclusions, restricted to scalars in R.
The tensor balancing identity proves commutativity of this cocone.
`affineTensorPushoutIsColimit` constructs its full universal property.
It forgets any target cocone to the corresponding ring cocone and uses
Mathlib's actual tensor pushout of commutative rings. The left inclusion
proves that the resulting ring map preserves R. The two factorization
equations and uniqueness are inherited from that ring universal property.

All four rings lie in a common arbitrary universe. No topology or
finite-generation assumption is imposed. This unit does not assert the
fibre-product topology axiom or a comparison with actual scheme points.
