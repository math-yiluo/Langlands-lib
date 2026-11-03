# Group structure on an actual normal fpqc coset quotient

This module constructs an actual group scheme on an existing normal fpqc
coset quotient and proves its exact represented kernel. It is derived
infrastructure for the ground-field unipotent-radical quotient proof.

## Inputs and scope

Let `S` be any scheme and `G` an actual group scheme over `S`. The inputs are a
subgroup functor `H`, normal on every relative scheme test, an actual scheme
`Q` over `S`, and a morphism `q : G.X ⟶ Q` which is quasi-compact, flat and
surjective. The fiber hypothesis says, for every `T : Over S` and every pair
of `G`-points `g,h` over `T`,

```
g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T.
```

The construction imposes no field, smoothness, affineness, connectedness or
representability assumption on `H`. It does assume that the quotient scheme
and the stated morphism already exist. The last theorem additionally assumes
local finite presentation of `q.left`.

## Descent of the operations

`mul_preserves_fibers` proves two-sided compatibility using normality: if
`a⁻¹a'` and `b⁻¹b'` belong to `H(T)`, then the product of the conjugate
`b⁻¹(a⁻¹a')b` with `b⁻¹b'` belongs to `H(T)`. This is
`(ab)⁻¹(a'b')`. For inversion, the conjugate by `a` of `(a⁻¹b)⁻¹`
is `ab⁻¹`, giving `inv_preserves_fibers`.

These identities are transferred to maps from arbitrary underlying schemes
by viewing each source over `S` through its composite structure map.
`effectiveEpi_tensorHom` proves that the underlying morphism of `q ⊗ₘ q`
is an effective epimorphism: the product morphism is fpqc by stability under
base change, and Mathlib's scheme fpqc descent supplies the instance.

`mulSchemeHom` descends the composite of multiplication in `G` with `q`
along `q ⊗ₘ q`; `invSchemeHom` descends inverse followed by `q` along `q`.
Their factorization identities also show that the descended maps lie over
`S`, giving `mulHom` and `invHom`. The quotient unit is `η[G.X] ≫ q`.

`mulPoint_lift` and `invPoint_lift` compute the operations on lifted points:
the product of `a ≫ q` and `b ≫ q` is `(a*b) ≫ q`, and the inverse
of `a ≫ q` is `a⁻¹ ≫ q`. The point operations are natural under every
map of test schemes.

## Group structure and homomorphism

The unit, associativity and both inverse laws hold on every test scheme.
They are checked after successive pullbacks along `q`, using
`Dynamic.flagQuotient_hom_ext_of_local_lift`. Each pullback projection is
epimorphic; hence equality after those pullbacks gives equality of the
original morphisms. This argument never requires an original test point to
have a global lift.

`groupObj` packages these point laws as Mathlib's categorical `GrpObj Q`.
The unit laws are evaluated on the product projections and matched with the
unitors. Associativity is evaluated on the three projections from
`(Q ⊗ Q) ⊗ Q` and matched with the associator. The inverse laws are
evaluated at the identity morphism of `Q`. Consequently `groupScheme` has
exactly the original underlying scheme `Q` and the descended structure maps.
`hom` is the original projection packaged as a group-scheme homomorphism;
`hom_hom` states that its underlying morphism is `q`.

## Exact represented kernel

`range_kernel` proves the equality of subgroup functors

```
SubgroupFunctor.range (kernelι (hom G H hn q hfib)) = H.
```

For every test `T`, the fiber criterion applied to the identity and `x`
identifies `x ≫ q = 1` with membership in `H(T)`. The published
`kernelPointsEquiv` sends any represented kernel point to such an `x`.
Conversely, the published kernel pullback constructs a represented kernel
point from every `x` with `x ≫ q = 1`. Extensionality on every test scheme
then proves the claimed equality.

With local finite presentation of `q.left`, `isFppfQuotient` combines this
equality with the original flatness and surjectivity to prove the unchanged
predicate `RelativeRoot.IsFppfQuotient H (hom G H hn q hfib)`.

## Provenance and remaining obligations

This is an internal derivation from the published subgroup functor, actual
kernel and fpqc local-lift interfaces, together with Mathlib's effective
epimorphism descent and Cartesian monoidal group objects. No external
mathematical assertion is taken as an axiom or assumed theorem field.

This unit does not construct the original quotient scheme or prove its
affineness, smoothness, connectedness or pseudo-reductivity. In particular,
it does not by itself prove `UnipotentRadicalQuotientStatement`.
