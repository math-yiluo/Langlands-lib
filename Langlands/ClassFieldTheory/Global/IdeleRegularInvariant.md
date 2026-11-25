# Invariants on regular classes from compatible idele invariants

This derived supporting module implements the regular-class construction
in Artin–Tate, *Class Field Theory* (2009), Chapter VII §3, printed
pp.47–49: Remarks 1–3, the definition of regularity and its invariant,
and Lemma 4. It uses the actual idele and idele-class cohomology and the
published regular subgroup. The input family of idele invariants is
explicit. The module does not construct that family from local
invariants, prove reciprocity, or prove `GlobalInvariantStatement`.

`IdeleInvariantMaps` is the type of additive maps from actual
`H²(Gal(E/F), J_E)` to the rationals modulo integers, for all Galois
number-field extensions in one arbitrary universe. It has no built-in
laws. Three proposition definitions express that these maps kill the
kernel of the actual idele-to-idele-class map, preserve actual
inflation, and multiply by the base-extension degree under actual
restriction. The restriction law allows nonnormal intermediate fields.

Given kernel vanishing and inflation compatibility,
`regularIdeleClassInvariant` constructs an additive map on each actual
regular subgroup. A regular class has an idele representative after
inflation to some finite Galois extension. The implementation first
chooses a value furnished by one such representative. To compare it
with any other representative, it embeds both witnessing extensions
in their common Galois overfield over `E`. Transitivity and the
quotient-inflation square make the two inflated idele classes have the
same quotient class. Kernel vanishing applied to their difference
makes their invariants equal, and inflation compatibility returns this
equality to the original representatives.

Zero uses the zero representative. For addition, the published
common-extension theorem puts two regular classes in one witnessing
extension; the sum of their representatives represents the sum.
Independence of representatives and additivity of the supplied idele
map then prove additivity.

`regularIdeleClassInvariant_eq` computes the result from any witnessing
extension and any idele representative there.
`regularIdeleClassInvariant_apply_quotient` shows that the constructed
map agrees with the supplied map on classes already represented by
ideles. `regularIdeleClassInvariant_inflation` proves inflation
compatibility by using one representative for the inflated class and
transitivity to regard it as a representative for the lower class.

If the supplied maps additionally satisfy the restriction law,
`regularIdeleClassInvariant_restriction` proves the same law for the
constructed regular invariants. It restricts a witnessing idele class,
uses the quotient-restriction square and inflation-restriction
compatibility to identify its class, then applies the supplied degree
formula. No injectivity of an invariant or surjectivity of the general
idele-to-idele-class map is assumed.

The family and its three explicit proposition definitions are internal
interfaces for this construction. In the intended application, the
family is the sum of local invariants, kernel vanishing comes from
reciprocity and the coefficient exact sequence, and the two
compatibilities come from the local invariant laws. Those arithmetic
inputs are not discharged here.
