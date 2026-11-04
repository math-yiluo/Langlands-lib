# Dimension comparisons for actual scalar-extension algebras

This unit supplies two prerequisites for the dimension condition in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(2). The registered Conrad source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The separate algebraic comparisons are not stated there.

`FiniteTypeFieldExtensionRingDimensionInvariance` states that, for a field
extension K/k and a finitely generated commutative k-algebra A,
the total ring Krull dimensions of A and the actual tensor-product algebra
K ⊗[k] A agree. This is the result of the Stacks Project, Lemma 10.116.5,
tag 00P3, registered as `stacks-dimension-field-extension-00p3-2026-11-04`,
SHA-256 `a952d5dbca6b120b89152bcdcace6f4ad5557de8266de7882430c1954c4d898c`.
The tensor product is Mathlib's ordinary algebra tensor product. The field
extension need not be algebraic, finite or separable. A need not be reduced,
a domain, or nonzero. Ring Krull dimension has values in WithBot ENat,
and a zero ring has dimension bottom.

`AlgebraicFieldExtensionPureRingDimensionInvariance` is an internal
consequence of the flat-integral invariance prerequisite. For an algebraic
extension K/k, an arbitrary commutative k-algebra A, and any natural d,
it states that A has pure ring dimension d if and only if A ⊗[k] K does.
There is no finite-type assumption in this assertion. The extension can be
infinite and inseparable. Pure dimension means that every quotient by an
actual minimal prime has ring Krull dimension d; for a zero ring this is
vacuous. The map A → A ⊗[k] K is the canonical scalar-extension map. It is
flat, integral and injective, which explains the internal provenance.
The two tensor orientations used in the statements follow the respective
standard scalar-extension and integral-base-change conventions.

`FieldExtensionDimensionComparisons` is exactly the conjunction of these
two propositions. In every proposition k, K and A have independent
universes u, v and w. No topology or arbitrary auxiliary presentation is
used. The general finite-type pure-dimension comparison under arbitrary
field extension, scheme fibre comparisons, constructibility, and filtered
descent remain separate obligations.
