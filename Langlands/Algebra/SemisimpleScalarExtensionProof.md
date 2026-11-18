# Semisimplicity after scalar extension

`Langlands.Algebra.semisimpleScalarExtension` proves
`Langlands.Algebra.SemisimpleScalarExtensionStatement` with independent universes
for the fields `k` and `K` and the algebra `A`. It covers both a separable
algebraic extension `K/k` and an arbitrary field extension of `k` when the
centre of `A` is étale over `k`.

The proof uses Mathlib's algebra form of Wedderburn–Artin to decompose `A` into
a finite product of finite-dimensional simple matrix algebras `B i`. In the
étale case, it transports formal étaleness along the induced equivalence of
centres. The centre of the product is the product of the centres of the `B i`,
so `Algebra.FormallyEtale.pi_iff` gives formal étaleness for each centre.

For each simple factor `B`, its centre `Z` is a field, finite-dimensional over
`k`. The algebra `B` is central simple and finite-dimensional over `Z`. The
tensor product `C = Z ⊗[k] K` is finite-dimensional over `K` and is therefore
Artinian. The proof shows that `C` is reduced in both cases.

- For separable algebraic `K/k`, Mathlib's flat tensor-product reduction tests
  reducedness on finitely generated `k`-subalgebras of `K`. Each is the
  underlying subalgebra of a finite separable intermediate field. Its tensor
  product with `Z` is formally unramified over the field `Z`, hence reduced.
  This argument applies to extensions of arbitrary degree.
- For formally étale `Z/k`, formal unramifiedness gives reducedness of
  `K ⊗[k] Z` over the field `K`, and the tensor flip gives reducedness of `C`.

The Artinian decomposition of the reduced commutative ring `C` gives a finite
product of residue fields `F i`. The tensor associator and unit and flip
equivalences identify `K ⊗[k] B` with `C ⊗[Z] B` as a ring. Distributing the latter
tensor product over the residue fields gives the factors `F i ⊗[Z] B`.
`Langlands.CentralSimple.isSimpleRing_baseChange` makes each factor simple.
Each factor is finite-dimensional over `F i`, so it is Artinian and therefore
semisimple. Distributing the original tensor product over the Wedderburn–Artin
product then gives semisimplicity of `K ⊗[k] A`. The zero algebra is covered by
the empty Wedderburn–Artin product.

This is the internal algebra prerequisite for the operator-algebra approach to
Milne, *Algebraic Groups* (2017), Proposition 4.19(c), pp. 90–91. The structural
algebra results underlying the proof appear in Theorems 24.16–24.19, p. 518, of
the same book (registered source `milne-2017-algebraic-groups`).
