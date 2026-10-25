# Conjugation of concrete block pairs

This is a derived construction over a commutative ring `R` in an arbitrary
universe and any rank `n`. A concrete pair `P : ConjugateBlockPair n R` has an
ordered block shape `B = P.shape` and a conjugator `c = P.conjugator`.
`P.conjugateBy y` retains `B` and replaces `c` by `y*c`, for an arbitrary
ambient invertible matrix `y`.

## Actual subgroup transport

The following identities are proved for this construction:

- `conjugateBy_parabolic`: the actual parabolic of the new presentation is
  `P.parabolic.map (MulAut.conj y).toMonoidHom`.
- `conjugateBy_scalarMap`: its block-scalar homomorphism is the composite of
  `P.scalarMap` with conjugation by `y`.
- `conjugateBy_splitComponent`: its actual split component is
  `P.splitComponent.map (MulAut.conj y).toMonoidHom`.
- `conjugateBy_leviEmbedding`: its Levi embedding is the composite of
  `P.leviEmbedding` with conjugation by `y`.
- `conjugateBy_leviSubgroup`: its embedded Levi subgroup is
  `P.leviSubgroup.map (MulAut.conj y).toMonoidHom`.

The proofs expand conjugation and use associativity and `(y*c)⁻¹ = c⁻¹*y⁻¹`.
The subgroup equalities follow from composition of subgroup maps or from the
range of a composite homomorphism. All subgroups are the actual subgroups of
`GeneralLinear n R`, rather than abstract isomorphic copies.

## Consequences of a matrix standardizer

The remaining four theorems assume an actual `m : B.Levi R` and the equation

```text
y * P.conjugator = B.leviEmbedding R m.
```

`parabolic_map_conj_of_standardizer` proves

```text
P.parabolic.map (MulAut.conj y).toMonoidHom = B.parabolic R.
```

After the transport identity, conjugation is by `B.leviEmbedding R m`.
This matrix lies in the standard parabolic through `B.leviInParabolic`, so it
normalizes that subgroup.

`scalarMap_conj_of_standardizer` proves the stronger pointwise identity

```text
y * P.scalarMap a * y⁻¹ = B.blockScalar R a
```

for every block-unit tuple `a`. The published `blockScalarLevi_commute` says
that block scalars commute with every element of the product Levi. Applying
the Levi embedding gives the required matrix commutation, and the standardizer
equation reduces the conjugation expression to that calculation.

`splitComponent_map_conj_of_standardizer` takes ranges of this pointwise
identity and uses `standard_scalarMap` to prove

```text
P.splitComponent.map (MulAut.conj y).toMonoidHom =
  (ConjugateBlockPair.standard B).splitComponent.
```

`leviSubgroup_map_conj_of_standardizer` proves

```text
P.leviSubgroup.map (MulAut.conj y).toMonoidHom = B.leviSubgroup R.
```

The range of the transported Levi map is the standard embedded Levi conjugated
by `B.leviEmbedding R m`. This matrix belongs to that subgroup, and hence
normalizes it.

## Provenance and scope

This unit derives its construction and identities from the published
`Representation.Exponents.ParabolicPair`, `Representation.Induction.ConjugateParabolic`,
and `Group.GL.BlockIwahoriDefinitions` definitions and laws, together with
Mathlib subgroup-map and normalizer facts. It claims no independent source
result. The general ring hypotheses include rank zero; no semistandard,
representation, topology, or field condition is needed for these identities.

The standardizer equation is supplied, not constructed here. The module proves
neither its existence from semistandardness nor any permutation property,
normalizer classification, or Langlands data recovery. Those remain distinct
obligations of the parent semistandard conjugacy task.
