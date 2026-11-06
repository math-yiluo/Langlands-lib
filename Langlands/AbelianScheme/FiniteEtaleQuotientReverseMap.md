# Reverse maps of finite étale quotients with bounded kernel

Author: Worker 1575.

This internal construction supplies the quotient and reverse-map step of
commensurable full Tate lattice realization. It generalizes the specialized
reverse-map construction in `Langlands.AbelianScheme.OrderSaturation` by taking
any actual finite étale subgroup killed by the specified natural number.
It relies only on published quotient and isogeny factorization interfaces.
No external source theorem is asserted or cited.

## Supplied quotient

Let `A` be an actual abelian scheme over an arbitrary scheme `S`, let
`K : FiniteEtaleSubgroup A`, and let `D : K.QuotientData`. The data contain an
actual quotient abelian scheme `D.B`, a finite étale surjective homomorphism
`D.q : A ⟶ D.B`, and the cartesian square identifying `K` with its scheme
kernel.

For a natural number `N`, assume the scheme-level annihilation equality

```text
K.inclusion ≫ commHom (N • 𝟙 A) = 0.
```

In the namespace `Langlands.AbelianScheme.FiniteEtaleSubgroup.QuotientData`,
`inverseMultiple D N hK` applies the existing universal quotient lift to
multiplication by `N`. It is an actual homomorphism `r : D.B ⟶ A`.
The factorization law gives `q ≫ r = N • 𝟙 A`.
To prove `r ≫ q = N • 𝟙 D.B`, the implemented proof precomposes both sides
with the isogeny `q`, uses the first equation and bilinearity of composition,
and cancels `q` using `IsogenyActionDescent.hom_ext`.
`inverseMultiple_unique` uses the same cancellation to show that the first
equation uniquely determines `r`.

These constructions and equations allow `N = 0`. Rational invertibility
requires `0 < N`: `inverseData` packages the two maps and equations as the
existing `Rationalization.IntegralInverseData A D.B`, with integer multiple
`(N : ℤ)`. Its `toIso` is exposed as `rationalIso`, whose forward map is
`Rationalization.ofHom q` and whose inverse is
`(N : ℚ)⁻¹ • Rationalization.ofHom r`. The two formula lemmas are
`rationalIso_hom` and `rationalIso_inv`.

## Constructing the quotient

`exists_quotient_inverseMultiple_of_forall_finset_fibre` additionally assumes
that `S` is locally noetherian and that every finite set of points in a
single fibre of `A` is contained in an affine open of `A`. With the same
given `K`, `N` and annihilation equality, it constructs quotient data `D` and
an actual reverse map `r` satisfying both equations. It applies
`FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre`
to obtain `D`, then uses the supplied-quotient construction above.

The quotient abelian scheme and all maps remain over the entire original
base. The result assumes no quotient, reverse map, projective embedding,
connectedness, geometric point or Tate image comparison. The subgroup and
its annihilation remain inputs to this focused helper. Deriving them from
a monodromy-invariant lattice and proving its final Tate image equality
are separate steps in the parent task.

This generic quotient construction is located beside
`FiniteEtaleQuotient` and `IsogenyActionDescent`; its Tate-image consumers
import it from `Langlands.AbelianScheme.FiniteEtaleQuotientReverseMap`.
