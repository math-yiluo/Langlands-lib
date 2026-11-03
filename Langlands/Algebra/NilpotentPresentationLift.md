# Lifting prescribed presentations through nilpotent base reduction

Let `A → B` be a homomorphism of commutative rings, `I` a nilpotent ideal
of `A`, `J = IB`, and `C = B/J`. Let `M` be an existing `B`-module with
a compatible `A`-action that is flat over `A`. Given natural numbers
`n,m` and an actual prescribed finite free presentation

```text
C^m --g₀--> C^n --f₀--> M/JM --> 0,
```

`liftFiniteFreePresentationOfNilpotentQuotient` chooses `B`-linear maps
`g : B^m → B^n` and `f : B^n → M`. It returns the actual pair of maps
with proofs that `f` is surjective, `image g = kernel f`, and, for every
vector of coefficients, their reductions equal the prescribed maps:

```text
class(f(x)) = f₀(class(x)),
class(g(y)) = g₀(class(y)).
```

Here `class` on a free module means coordinatewise reduction by `J`,
and on `M` it means the ordinary quotient map to `M/JM`. This quotient
has the standard `C`-module action. Both ranks are exactly the given
`n,m`, including when one is zero. The choices are not asserted to be
unique or functorial.

`liftFiniteFreePresentationOfBaseNilpotent` gives the tensor formulation.
Its inputs are the prescribed `C`-linear maps

```text
C ⊗[B] B^m --g₀--> C ⊗[B] B^n --f₀--> C ⊗[B] M --> 0.
```

Its output retains the same ranks, surjectivity and exactness and the
equalities of actual linear maps
`f.baseChange C = f₀` and `g.baseChange C = g₀`. The ordinary-quotient
constructor transports this data through the canonical finite-free
tensor equivalences and `quotientTensorEquiv`. Their formulas on
`1 ⊗ x` give the two coordinate reduction identities above.

The assumptions impose no Noetherian condition, finite generation of
the ideal, or flatness of `B` over `A`. Nilpotence means that one power
of the whole ideal vanishes. `A`, `B`, and `M` can lie in independent
universes. A finite-presentation assumption on `M` is not an input:
the prescribed reduced presentation and base-flatness suffice.

The construction uses three preliminary facts. For any commutative ring
`R`, ideal `L`, and module `N`, `quotientTensor_unit_surjective` proves
surjectivity of `N → (R/L) ⊗[R] N`, `x ↦ 1 ⊗ x`, using the canonical
comparison with `N/LN`. For any projective `R`-module `P`,
`liftMapOfQuotientTensor` therefore lifts any `(R/L)`-linear map from
the reduction of `P` to that of `N` to an actual `R`-linear map, with
equality of its tensor reduction. Neither assertion requires
nilpotence or flatness. Finally,
`surjective_of_nilpotent_baseChange` detects surjectivity of an arbitrary
linear map after tensor reduction by a nilpotent ideal, with no finiteness
assumption on either module. The reduced range is the whole quotient;
the nilpotent generation criterion then makes the original range the
whole module.

To lift a presentation, first lift `f₀` using projectivity of `B^n`.
Nilpotent detection makes this lift `f` surjective. Put `K = kernel f`.
Base-flatness of `M`, through
`reduction_injective_of_exact_of_base_flat`, makes
`C ⊗[B] K → C ⊗[B] B^n` injective. Tensor right exactness identifies
its image with `kernel f₀`. Thus the prescribed `g₀` factors through
`C ⊗[B] K`; this factor is surjective because the prescribed sequence
is exact. Lift the factor using projectivity of `B^m`, and apply
nilpotent detection again to obtain a surjection `B^m → K`. Composing
with the actual kernel inclusion gives `g`, proves exactness, and
recovers exactly the prescribed reduced map.

This is an internal construction from the imported nilpotent generation
criterion, the comparison of base reductions with a base-flat cokernel,
and Mathlib's projective lifting property and tensor right exactness.
It strengthens the earlier choice of arbitrary presentation ranks by
preserving a specified presentation. The module `M` and its flatness
are given; the construction does not create a module deformation.
Sheaf lifting and the coherent-family scheme atlas require additional
geometric arguments.
