# Rational formal Hom and quasi-isogenies

`RationalHom F M N` is the actual tensor product
`F ⊗[O] ModuleLaw.Hom M N`. The field is written on the left to use
Mathlib's canonical F-module structure. `sourceTensorEquiv` is the
canonical O-linear equivalence to `Hom M N ⊗[O] F`, the order used in
Drinfeld's definition. `ofHom` sends an integral homomorphism `f`
to `1 ⊗ f`; injectivity is not asserted without further hypotheses.

Composition is constructed by tensoring multiplication in `F` with
the O-bilinear composition of integral formal homomorphisms. On pure
tensors it is
`(a ⊗ g) ∘ (b ⊗ f) = (a*b) ⊗ (g ∘ f)`.
The tensor identities prove associativity and the identity laws, and
composition is F-bilinear. Coefficient extension is induced by scalar
extension of the integral coefficient-change linear map.
These constructions work for any field O-algebra `F`.

When `O` is an integral domain and `F` is its fraction field,
`QuasiIsogeny F M N` consists of a rational homomorphism and a
two-sided inverse. The module constructs identity, inverse and
composition of quasi-isogenies and the quasi-isogeny of an integral
formal O-module isomorphism. The inverse rational homomorphism is
unique.

The source is Drinfeld, *Coverings of p-adic Symmetric Regions* (1976),
§2 A, opening paragraph, printed p.109, where a quasi-isogeny is an
invertible element of `Hom(X,Y) ⊗_O K`. This is its finite-coordinate
implementation, generalized to integral domains and their fraction
fields. The tensor order, bilinear constructions and proofs by tensor
induction are derived implementation choices. The base ring here is
an arbitrary commutative O-algebra; the source's local-field setting
and uniformizer-nilpotent bases are special cases. Heights, rigidity
under nilpotent thickenings, and local gluing remain subsequent work.
