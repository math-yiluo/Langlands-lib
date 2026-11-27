# Separable generators over a dense subfield

Let `F` be a complete ultrametric normed field and let `K → F` be a dense field embedding.
`Langlands.FieldTheory.exists_separable_generator_of_denseRange` shows that a finite separable
extension `E/F` has a primitive element in `E` that is separable over `K`.
`Langlands.FieldTheory.adjoin_separableClosure_of_denseRange` gives the corresponding equality
of intermediate fields in an arbitrary overfield `L/F`. Adjoining the elements of `L`
separable over `K` to `F` gives the separable closure of `F` in `L`.

In the nondiscrete case, `CountableGaloisFamily.exists_dense_generator` supplies a primitive
element `y` whose monic equation has coefficients in the image of `K`. The proof applies that
result to a copy of `E` in the universe of `F` and transfers the generator and its equation
along the algebra equivalence. Lifting the coefficients gives a monic equation over `K`.
[Krasner's density argument](CountableGaloisFamily.md)

Let `q` be the exponential characteristic of `K`, which is also that of `F`. The minimal
polynomial of `y` over `K` is irreducible and is the expansion of a separable polynomial
along `X ↦ X^(q^m)` for some `m` (`Irreducible.hasSeparableContraction`). Its
separable contraction vanishes at `y^(q^m)`, so this power is separable over `K`. The power
generates the same field over `F` as `y` by
`IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable'`. In the discrete
case the dense embedding is surjective, so `F/K` and then `E/K` are separable.

For the intermediate-field equality, separability over `K` implies separability over `F`
by the scalar tower. Conversely, for an element `x` separable over `F`, apply the generator
result to `F(x)/F`. Its generator lies in the separable closure of `K` in `L` and generates a
field containing `x`.

The approximation is the coefficient-perturbation application of Krasner's lemma described
by Serre, *Local Fields*, Chapter II, §2, exercises 1–2, p. 30
(`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`). The use of a separable
contraction is an algebraic step after approximation and handles arbitrary coefficient
characteristic.
