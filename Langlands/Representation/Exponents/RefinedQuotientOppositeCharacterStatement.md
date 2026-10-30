# Scalar characters of upper refined quotients occur in opposite Jacquet modules

Author: Worker 728, for task `60d65200-028a-4089-b838-ae9a52a64862`
revision 1. Worker 510 isolated the interface and specified it.

`Langlands.Exponents.RefinedQuotientOppositeCharacterStatement.{uF,uV,uW}` is
a closed Prop-valued definition. It states an interface and proves nothing.
It does not assume, and is not, second adjointness. No theorem or
proposition definition in this module establishes the property it states.
The exact proposition is proved separately by
`Langlands.Exponents.refinedQuotientOppositeCharacter` in
`Langlands.Representation.Exponents.RefinedQuotientOppositeCharacterProof`;
see "Proof status" below.

## Exact statement and actual objects

The universes of the field `uF`, of the inducing carrier `uV` and of the
quotient carrier `uW` are independent. The proposition quantifies

- every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{uF} p` and
  every `T : F.TopologicalData`; the local instance `letI := T.topology`
  supplies the topology used by admissibility and by the open-kernel
  conclusion;
- every positive rank `n`, every standard block shape
  `B : GeneralLinear.BlockShape n` and every refinement
  `S : Geometric.BlockRefinement B`, including the unrefined one;
- every actual representation `σ : Rep.{uV} ℂ (Geometric.refinedLevi F.Carrier B S)`
  of the common refined Levi subgroup of the product Levi `B.Levi F.Carrier`,
  and every actual representation `π : Rep.{uW} ℂ (B.Levi F.Carrier)`;
- every character `χ : (Fin (B.flatten S).length → F.Carrierˣ) →* ℂˣ`.

The local `let` names the actual scalar homomorphism

```lean
z := (Geometric.flattenedLeviEquiv F.Carrier B S).toMonoidHom.comp
  ((B.flatten S).blockScalarLevi F.Carrier)
```

It sends a tuple `a` to the block-scalar element `(a_k · 1)_k` of the
flattened product `(B.flatten S).Levi F.Carrier`. It then maps that element
into `refinedLevi F.Carrier B S` by the existing multiplicative equivalence.
The flattened block `k` is the inner block `(i, j)` given by
`(B.flattenBlockEquiv S).symm k`, as in `Geometric.FlattenedLevi`.

The hypotheses are exactly the following.

1. `IsAdmissible σ.ρ` and `IsAdmissible π.ρ`; the Library's admissibility
   includes smoothness.
2. `Nontrivial π.V`: the carrier of `π` has a nonzero vector.
3. `Classification.HasScalarCharacter σ.ρ z χ`, that is,
   `σ.ρ (z c) v = (χ c : ℂ) • v` for every tuple `c` and every vector `v` of
   the whole carrier of `σ`.
4. There is an actual intertwiner
   `q : (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ` with
   `Function.Surjective q`.

The conclusion is the conjunction of

```lean
IsOpen (χ.ker : Set (Fin (B.flatten S).length → F.Carrierˣ))
```

and

```lean
IsGeneralizedEigencharacter
  ((T.normalizedRefinedOppositeJacquet B S π.ρ).comp z) χ
```

The character in the conclusion is `χ` itself. The scalar map `z` and the
flattened ordering are the same as in the hypothesis. The topology on the
tuple group is the product topology of the unit-group topologies from
`T.topology`; `T.IsJacquetExponent` states its open-kernel condition the
same way.

`IsGeneralizedEigencharacter` is the existing predicate of
`Langlands.Representation.Exponents.Jacquet`: there is one `k` with
`characterSpace _ χ k ≠ ⊥`. The character space is the intersection over
all tuples `a` of the generalized eigenspaces of power `k` of the operators
at `a` for the eigenvalues `χ a`. Hence one nonzero vector is killed by the
same power of every shifted operator. The predicate is not pointwise
spectral membership. It does not select a subquotient or use a dual
character.

## Actual constructions and normalization

`T.normalizedRefinedInduced B S σ.ρ` is the Library's actual upper normalized
refined induction from `Geometric.RefinementFunctors`. It consists of the
smooth functions on the product Levi that are left covariant under the
refined upper parabolic, with the twist by
`T.refinedParabolicHalfModulus B S`. This twist is the positive half
`δ_P^(1/2)` of the upper full modulus `T.refinedLeviModulus B S`, pulled back
through the Levi projection. The product Levi acts by right translation.

`T.normalizedRefinedOppositeJacquet B S π.ρ` from
`Parabolic.OppositeRefinementFunctors` is the actual quotient of `π` by the
refined lower (opposite) radical, `Geometric.RefinedOppositeJacquetModule B S π.ρ`,
with the refined Levi acting through its radical normalizer. The action is
twisted by the inverse half of the published full opposite modulus
`T.refinedOppositeLeviModulus B S`, defined as the inverse of
`T.refinedLeviModulus B S`. By `inverseHalf_refinedOppositeLeviModulus` this
twist equals the positive upper half `T.refinedLeviHalfModulus B S`. On
quotient classes, `normalizedRefinedOppositeJacquet_mk` gives

```
m · [v] = δ_P(m)^(1/2) [π(m) v].
```

The statement uses these constructions unchanged. It does not introduce a
replacement carrier, modulus or normalization.

## What is not assumed

The hypotheses contain no second adjointness, no nonzero or injective
Jacquet map, no Jacquet occurrence, no pairing, no finite series and no
irreducibility of `σ` or `π`. They contain no cuspidality, unitarity of `χ`,
real-part condition or analytic criterion either. Scalar action of `χ` on
the whole source `σ` replaces irreducibility. Nontriviality of `π` excludes
the zero target, for which the conclusion would fail: a zero opposite
Jacquet module has no nonzero vector. Nontriviality of `σ` is not assumed. It
follows from the hypotheses, because a zero `σ` has zero induction, which
has no surjection onto a nontrivial carrier.

## Internal provenance

This is an internal derived interface. It needs no external citation, and
none is made. Worker 510 isolated it from the support proof task
`9af5b508-2ac3-4243-8c36-2d40f55ab5bc`. Its upper cuspidal quotient must be
tied to an actual exponent before cone arguments apply. The statement is a
consequence of refined second adjointness together with linearity, scalar
equivariance, smoothness and continuity. The Library states refined second
adjointness as
`Langlands.Parabolic.RefinedSecondAdjointnessClause` in
`Langlands.Representation.Parabolic.SecondAdjointnessStatement`. That clause
is stated for the same functors and at the same universes `uF`, `uV`, `uW`.
Its own Markdown records its provenance. It is the second conjunct of
`Langlands.Parabolic.NormalizedSecondAdjointnessStatement`, which
`Langlands.Parabolic.normalizedSecondAdjointness` in
`Langlands.Representation.Parabolic.SecondAdjointnessProof` proves. Thus
`normalizedSecondAdjointness.2` proves the refined clause, with all of its
admissibility hypotheses. The derivation runs as follows.

1. Since `π.V` is nontrivial and `q` is surjective, `q ≠ 0`.
2. Refined second adjointness gives a complex-linear equivalence
   `E : Hom(i_upper σ, π) ≃ Hom(σ, r_opposite π)` for admissible `σ` and `π`.
   A linear equivalence sends the nonzero `q` to a nonzero intertwiner
   `E q : σ → r_opposite π`. Choose `v` with `w := E q v ≠ 0`.
3. Because `E q` is an intertwiner and `χ` acts by scalars on all of `σ`,
   `r_opposite(π)(z c) w = E q (σ(z c) v) = E q ((χ c) • v) = (χ c) • w`
   for every tuple `c`. Then `isGeneralizedEigencharacter_of_eigenvector`
   gives the second conjunct with power one.
4. The opposite Jacquet action is smooth by
   `T.isSmooth_normalizedRefinedOppositeJacquet`, so an open subgroup `U` of
   the refined Levi fixes `w`. The map `z` is continuous: it is the
   composite of the block-scalar map (continuous coordinatewise through
   `GeneralLinear.scalarContinuous`) with the underlying map of
   `Geometric.flattenedLeviEquivContinuous`. Hence `z⁻¹(U)` is an open
   neighbourhood of the identity. For `c` in it, `w = (χ c) • w` with
   `w ≠ 0`, so `χ c = 1`. The kernel of `χ` is a subgroup containing an open
   neighbourhood of the identity, hence open. Smoothness of `σ`, applied to
   `v`, gives the same conclusion.

This route needs neither an injective Jacquet map nor an irreducible source.
None of its ingredients may be added as a hypothesis of this closed
statement. The proposition definition above is not a theorem.

## Proof status

`Langlands.Exponents.refinedQuotientOppositeCharacter`, in
`Langlands.Representation.Exponents.RefinedQuotientOppositeCharacterProof`,
has type exactly `RefinedQuotientOppositeCharacterStatement.{uF,uV,uW}` and
adds no hypothesis. It implements the four steps above, applying them to the
actual quotient map `q` and the actual character `χ`. It obtains `E` from
`Langlands.Parabolic.normalizedSecondAdjointness.{uF,uV,uW}.2` at the given
`B` and `S`. The intertwining property of `E q`, combined with the scalar
action of `χ`, gives the eigenvector, and `isGeneralizedEigencharacter_of_eigenvector`
gives the second conjunct. For the open kernel, a private lemma uses the open
stabilizer of that eigenvector in the smooth opposite Jacquet module
(`T.isSmooth_normalizedRefinedOppositeJacquet`) and continuity of `z`, built from
`Geometric.flattenedLeviEquivContinuous` and `GeneralLinear.scalarContinuous`.
Second adjointness, the nonzero-map step and continuity are therefore proved,
not assumed.

## Scope and boundaries

The statement concerns only the occurrence of the scalar character in the
opposite Jacquet module of a quotient. It does not prove or state
opposite-to-upper analytic transport, a strict exponent criterion for
product Levis, central unitarity or real-part identities. It also says
nothing about generic cuspidal quotients, real unitarization of cuspidals
or the final support theorem. `T.IsJacquetExponent` concerns the upper
Jacquet module of a representation of `GL_n(F)`. This statement concerns
the opposite Jacquet module of a product-Levi representation, restricted to
the flattened block scalars of a refined Levi, so it does not by itself
produce an `IsJacquetExponent` witness.
