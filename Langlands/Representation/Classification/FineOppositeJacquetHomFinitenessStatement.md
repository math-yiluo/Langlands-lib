# Finite Hom spaces from actual fine twists into opposite Jacquet modules

Authors: Worker 833 and Worker 526. Worker 526 wrote the unreviewed proof
prototype whose theorem type this proposition transcribes; Worker 833 wrote
this statement pair.

`Langlands.FineOppositeJacquetHomFinitenessStatement.{uF,uV,uW,uZ}` is a
closed proposition definition with two conjoined clauses. This module states
the assertion; it contains no proof.

## Quantified data and hypotheses

The proposition quantifies over every prime `p` (as `[Fact p.Prime]`), every
p-adic field `F : PadicField.{uF} p`, and every compatible topological datum
`T : F.TopologicalData`. The installed topology is exactly `T.topology`; the
topologies of `GL_n(F)`, of the product Levi subgroups and of the refined
subgroup are the induced ones of the existing constructions. It then
quantifies over every natural rank `n`, including zero, every ordered block
shape `B : BlockShape n` and every refinement `S : BlockRefinement B`.

The fine input is an actual bundled complex representation
`ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)` of the flattened product
Levi. The only hypotheses on it are:

* `Representation.IsIrreducible ω.ρ`, the simple-order predicate on its
  actual subrepresentations;
* `CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ`, which is admissibility
  (including smoothness) together with vanishing of the actual unipotent
  coinvariants for every proper standard block refinement.

The real vectors `v₀ : Fin (B.flatten S).length → ℝ` and
`t : Fin B.length → ℝ` are arbitrary. No unitarity, positivity, strict
ordering, genericity or regularity condition is imposed on `ω`, `v₀` or `t`.

## The actual fine source

Put `τ := RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t`. This is the
existing actual representation of `Geometric.refinedLevi F.Carrier B S` on
the carrier of `ω`. Its action multiplies `ω` by the positive real character

```text
∏ k |det(m_k)|_F^(-v₀(k) + t(((B.flattenBlockEquiv S).symm k).1))
```

of the flattened product Levi, and is then pulled back along the inverse of
the constructed `Geometric.flattenedLeviEquiv F.Carrier B S`. The fine
exponents enter with a negative sign and the coarse exponents with a positive
sign, exactly as in that definition. The acting group of every Hom space
below is this actual refined subgroup of `B.Levi F.Carrier`.

## The two clauses

1. For every `π : Rep.{uW} ℂ (B.Levi F.Carrier)` with `IsAdmissible π.ρ`, the
   complex space `τ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)`
   is finite dimensional. The target is the existing normalized refined
   opposite Jacquet module: the coinvariant quotient of the carrier of `π` by
   `Geometric.refinedOppositeUnipotent F.Carrier B S`, the product of the
   inner lower radicals. The refined subgroup acts through its radical
   normalizer, twisted by the inverse half of
   `T.refinedOppositeLeviModulus B S`, the inverse of the full upper refined
   modulus. Equivalently, the normalizing scalar is the positive half
   `T.refinedLeviHalfModulus B S`.
2. For every `J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier)` with
   `IsAdmissible J.ρ`, the complex space
   `τ.ρ.IntertwiningMap (T.normalizedComposedOppositeJacquet B S J.ρ)` is
   finite dimensional. The target is the existing normalized composed
   opposite Jacquet module: the coinvariant quotient of the carrier of `J`
   by `Parabolic.composedOppositeUnipotent F.Carrier B S`, which contains the
   outer lower block radical and the embedded inner lower radicals. The
   refined subgroup acts through its embedding in `GL_n(F)`, twisted by the
   inverse half of `T.composedOppositeLeviModulus B S`; the normalizing
   scalar is the positive half `T.composedLeviHalfModulus B S`, which
   includes both the outer and the inner contributions.

`Langlands.IsAdmissible` means smoothness together with finite
dimensionality of the fixed vectors of every open subgroup; the carriers of
`π` and `J` may be infinite dimensional. `Representation.IntertwiningMap` is
Mathlib's space of all complex-linear maps commuting with the two actions of
the refined subgroup; no continuity is required. `FiniteDimensional ℂ` is
finiteness of that space as a complex vector space.

The field, fine source, coarse target and ambient target universes `uF`,
`uV`, `uW` and `uZ` are independent. The source carrier lies in `uV`, and the
two targets keep the carriers of `π` and `J`, in `uW` and `uZ`.

## Scope

The targets `π` and `J` are only assumed admissible: they need not be
irreducible, of finite length, tempered or quotients of any induced
representation. No support condition, quotient presentation, second
adjointness, Jacquet semisimplicity, finite-length theorem or chosen Hom
equivalence enters the statement. Each Hom space may be zero. The statement
asserts finite dimensionality only; it contains no equality or inequality of
dimensions and no comparison between the two clauses.

## Internal provenance

This is an internal specialization of existing published interfaces, not a
transcription of a statement in the original literature. In particular, the
two-clause shape and these Hom spaces are formalization choices; they are not
attributed to Silberger's 1978 article, and no Hom comparison is asserted.

The rationale is the following route through published results, which a
separate proof must still assemble:

* `Langlands.fineTwistIrreducibleAdmissible`, in
  `Classification.FineTwistRegularityProof`, proves that `τ` is irreducible
  and admissible, hence smooth.
* An irreducible representation makes its module over the group algebra
  `MonoidAlgebra ℂ (refinedLevi F.Carrier B S)` simple, hence finitely
  generated.
* `Langlands.finite_intertwiningMap_of_finiteType`, in
  `Smooth.IntertwinerFiniteness`, proves finite dimensionality of all
  intertwiners from a smooth source of finite type over the group algebra
  into an admissible target.
* The targets are admissible by
  `Langlands.Parabolic.isAdmissible_normalizedRefinedOppositeJacquet` and
  `Langlands.Parabolic.isAdmissible_normalizedComposedOppositeJacquet`, in
  `Parabolic.OppositeJacquetAdmissibilityProof`. Their original-source
  provenance is recorded with `OppositeJacquetAdmissibilityStatement`.

The statement imports only the modules defining its notions:
`Classification.RelativeJacquetMultiplicityStatement` for `fineTwist`, and
`Parabolic.OppositeRefinementFunctors` for the two normalized opposite
Jacquet representations. None of the proof modules above is imported.

## Intended use

The two clauses supply the finite-dimensionality inputs needed for the
actual fine Hom spaces in `Langlands.GLRelativeCosocleHomComparisonStatement`.
Applying them there still requires admissibility of the parent's target
representations and the transport along its flattening equality. This
statement does not prove the dimension equality of that parent statement.
