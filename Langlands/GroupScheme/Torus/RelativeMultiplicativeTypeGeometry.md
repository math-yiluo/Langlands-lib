# Geometry and fppf locality of relative groups of multiplicative type

Worker 879. Internal derived helpers for the canonical kernel-factorization
proof, using the published definition in
[`RelativeMultiplicativeType`](RelativeMultiplicativeType.md).

For an arbitrary scheme `S`, the relative multiplicative-type predicate
descends along every fppf cover. A relative group of multiplicative type is
affine, flat, locally of finite presentation, and commutative over `S`.
There is no smoothness or connectedness assertion; the character groups may
have torsion.

`IsMultiplicativeType.commGroupScheme` equips the original group scheme
with its proved commutativity as an actual `CommGroupScheme S`; its
underlying group scheme is definitionally the original one.

The locality proof chooses diagonalizing covers over each member of the
given cover, composes them with `ZeroHypercover.bind`, and transports the
diagonalizable models through `baseChangeCompIso`.

The geometry proofs first treat the split model `D_S(Λ)`. Affineness is
preserved by base change from `Spec ℤ`. The group algebra `ℤ[Λ]` is free
as a module, hence flat. When `Λ` is finitely generated, its group algebra
is of finite type over the noetherian ring `ℤ`, hence of finite presentation.
Base change gives these properties over `S`. The split model is a base
change of an actual commutative group scheme. Isomorphisms transport the
properties to arbitrary diagonalizable groups. Finally the published
fppf descent results for morphism properties and commutativity descend
them from a diagonalizing cover.

These are internal consequences of the Library constructions and descent
theorems, not new transcriptions of a literature assertion.

The shared module also exports `locallyOfFinitePresentation_integralModel` for
the integral diagonalizable model, `IsMultiplicativeType.commGroupScheme_toGrp`
for the unchanged underlying group, and the separatedness and quasi-compactness
consequences `IsMultiplicativeType.isSeparated` and
`IsMultiplicativeType.quasiCompact` of relative affineness.

The shared fppf-locality and commutativity declarations are provided by
`RelativeMultiplicativeTypeLocality`; this module imports and reuses them.
