# Normal simple-root data and powered root maps under scalar extension

This is internal derived support for the affine split Isogeny Theorem.
It adds wrappers around the published coordinate base-change comparisons.
Both the original coefficient ring `R` and its commutative algebra `A` are
arbitrary. Neither ring is assumed local, reduced or nonzero.

`NormalSimpleDataBaseChangeStatement` says that actual normal simple-root
data for an affine group scheme over `Spec R` pull back to normal data for
the canonical coordinate torus over `Spec A`. The root datum `P`, its base
`b`, its descending words `W`, and all root indices remain exactly the
same. The pulled-back family is `baseChangeRoot A ∘ v`.
`normalSimpleDataBaseChange` proves this proposition.

The wrapper `IsNormalSimpleData.baseChange` reuses the published transport
of reductivity, fibrewise maximal tori, the full fibrewise root datum, actual
root parametrizations and prescribed Weyl reflections. Descending words
are unchanged integral data. The missing forward wrapper
`RankOneNormal.baseChange` transfers both root conjugations and the coroot
square using the canonical point-group equivalence. Every affine test
over `A` is also a test over `R`. The original base-point square holds on
every scheme test by naturality of constant points and of the fixed
cocharacter coordinates; this supplies its square over `Spec A`.

For a root-datum isogeny `f`, `rootFactor_characteristic_baseChange`
transfers the original hypothesis
`f.rootFactor j ≠ 1 → (p : R) = 0` to `A` by the algebra map. With the
original and transferred characteristic hypotheses,
`baseChangeRoot_rootMap` proves equality of the actual powered root maps
through the canonical additive-line comparison. Its formula on every
scheme test is the same monomial with exponent `f.rootFactor j`.
The equality accepts any proof of the characteristic hypothesis over
`A`, so it does not constrain the proof term chosen by a caller.

`torusMap_baseChange` records the square for the prescribed integral
coordinate torus map over every scheme base change. It is the published
`exponentHom_baseChange` applied to the weight map of `f`.
`baseChangeHom_torusMap` expresses the resulting equality after composing
with any supplied target torus inclusion.

No local conjugation, commutator or gluing theorem is invoked here. These
comparisons allow a separate local-ring argument to use the same original
root data and descend its point identities; they do not construct the
ambient isogeny or prove the host theorem.
