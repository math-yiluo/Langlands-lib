# Reversing the minimal parabolic inside the actual Levi

Worker 248, Task 5460. `RationalLeviXiReversalStatement.{u}` is a Prop-valued
statement at arbitrary universe `u`, proved by `rationalLeviXiReversal`.
For a connected reductive group over a nonarchimedean local field, a maximal
split torus, generic cocharacter `nu`, and a simple-root face `J`, assume
that the supplied compact open `K` gives the minimal Levi decomposition

```
M_J(F) = (P0(F) intersect M_J(F)) (K intersect M_J(F)).
```

The theorem preserves this exact compact Levi factor after changing the
standard data to `(-nu,-J)`. The two actual Levi subgroups are equal. If `m`
and `n` are subtype presentations of the same ambient point in the old and
reversed Levis, the two `rationalLeviXi` values are exactly equal. No scalar
comparison factor appears. There is no ambient Iwasawa, structural basis,
Cartan covering, matrix height or analytic estimate among the premises.
The theorem uses the original Levi decomposition; it does not derive it
from an ambient decomposition.

The implemented proof works with the original intrinsic standard-Levi
scheme. First, every ambient generic cocharacter remains generic for its
torus because its relative roots form a subset of the ambient relative
roots. The dynamic closed-subgroup restriction theorem and the published
empty-face standard/dynamic comparison identify the intrinsic minimal
parabolic for any such cocharacter with the ambient minimal parabolic's
preimage. This also identifies the reversed intrinsic minimal parabolic,
without replacing the original Levi scheme.

The helper `standardLeviMinimalModulusOf_eq_modularCharacter` identifies
the actual minimal Levi modulus with the modular character of the actual
minimal Levi parabolic. It restricts the published intrinsic Levi point
equivalence to that parabolic, uses the published exact modulus transport,
and transports its modular character. Closedness supplies the required
locally compact parabolic topologies.

`IsIwasawaPair.reversedLevi` transports the supplied original decomposition
to the intrinsic Levi, applies the proved same-compact change of minimal
parabolic from `RationalXiChangeMinimal`, and transports the reversed
factorization back to the equal actual reversed Levi subgroup. The
compact subgroup is always the preimage of the same supplied `K`.

For spherical functions, `rationalXi_leviScheme_reversed` applies the
existing `xi_map` to the equivalence from original intrinsic Levi points
to reversed actual Levi points. The two parabolics and compact subgroups
match exactly. Their inducing characters agree by their modular-character
identities and invariance under continuous group isomorphisms. The
normalized compact Haar measure therefore transports with no constant.
Finally `rationalLeviXi_reversed` combines this identity, the original
published intrinsic Levi spherical identity, and the proved intrinsic
change-of-minimal-parabolic equality.

This is derived Library transport for the change of minimal parabolic
allowed by the remark after Waldspurger's Proposition II.4.5, printed
p.263. The definition of the intrinsic Levi spherical function is II.1,
printed p.252. Source: Waldspurger (2003), registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The module proves no analytic lower bound, weighted-integrability estimate,
or full constant-term estimate.
