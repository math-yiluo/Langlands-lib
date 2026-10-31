# Separated symmetrization spans the genuine enveloping algebra

Let `R : Type` be a field, `L : Type v` an `R`-Lie algebra, and
`P : Type w` an `R`-module. Write `U` for the genuine universal enveloping
algebra of `L`, and `ι` for its generator map. This internal construction
uses a linear map `f : P →ₗ[R] L` and a unital `R`-subalgebra `B` of `U`.
Neither module is assumed finite-dimensional, and `f` need not be injective.

The algebra homomorphism `symmetricLinearLift R L f` is the universal lift
`S(f) : S(P) →ₐ[R] S(L)`. Its formula on generators is
`S(f)(ι_P(p)) = ι_L(f(p))`. Composing with the published whole-algebra
symmetrization gives the linear map `linearFamilySymmetrize R L f`.

`separatedSymmetrization R L f B` is the linear map

```text
S(P) ⊗[R] B →ₗ[R] U,
a ⊗ b ↦ sym(S(f)(a)) * b.
```

The theorem `separatedSymmetrization_tmul` records this exact pure-tensor
formula, with the right factor coerced from the genuine subalgebra `B`.
These constructions require only the field assumption.

In characteristic zero, `separatedSymmetrization_surjective` proves that
this map is onto under the splitting hypothesis

```text
range(f) ⊔ ι⁻¹(B) = ⊤
```

as submodules of `L`. Here `ι⁻¹(B)` is the inverse image of the underlying
linear submodule of `B` under the linear generator map. Thus the hypothesis
says exactly that every Lie vector can be written as `f(p) + y` with
`ι(y) ∈ B`. It does not assert that this decomposition is unique.

The implemented proof shows by induction on `d` that the genuine enveloping
degree piece `F_d U` is contained in the range. At degree zero, a scalar is
the image of its symmetric-algebra scalar tensor the unit of `B`. The
published word-span description reduces the next step to a generator word
of length at most `d + 1`. Split each letter as above and expand by the
multilinearity of ordered words. Each resulting word has every letter in
`range(f)` or in `ι⁻¹(B)`.

For such a word, put the letters in `range(f)` first by a list permutation.
The published commutator comparison places the permutation error in degree
at most the original word length minus one. Replacing the first block by
its symmetrization has an error in the same bound: multiply its strict
symmetrization error by the second block. An empty first block has zero
error. The main term lies in the range of the tensor map because the first
symmetric monomial lifts along `S(f)` and the second enveloping word lies
in the subalgebra `B`. Both errors lie in `F_d U` and are covered by
induction. Exhaustiveness of the genuine filtration then gives surjectivity
on all of `U`.

The provenance is internal. The proof combines the published
`FilteredSymmetricAlgebraSymmetrization` word-span description with the
strict permutation and symmetrization comparisons of actual generator
words. It does not require PBW injectivity or a choice of basis. It asserts
surjectivity of this linear tensor map, with no algebra-homomorphism or
injectivity assertion. Specialization to Cartan and compact directions,
central generation, and automorphic differential growth are separate
obligations.
