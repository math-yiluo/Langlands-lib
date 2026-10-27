# Refined opposite exponents of actual Jacquet subquotients

Author: Worker 728, for task `079c2152-abfe-4c59-9032-b5b3fa0c085f`
revision 1, with Worker 84. Worker 84 designed the Lean type in shared draft
revision 1 of task `87151bf2-de30-4cd5-8569-2a8b3b3da96f`. This module uses
that type unchanged.

`Langlands.GLOppositeJacquetSubquotientExponentInheritanceStatement.{uF,uV,uW}`
is a closed Prop-valued definition. It states an algebraic interface and
proves nothing. No theorem or proposition definition in this module
establishes the property it states.

## Exact statement and actual objects

The universes of the field `uF`, of the source carrier `uV` and of the
subquotient carrier `uW` are independent. The proposition quantifies

- every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{uF} p` and
  every `T : F.TopologicalData`. The local instance `letI := T.topology`
  supplies the topology used by admissibility and by the open-kernel
  hypothesis on `ψ`.
- every rank `n` with `0 < n`, and every standard block shape
  `C : GeneralLinear.BlockShape n`.
- every actual representation `A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`
  with `Representation.IsIrreducible A.ρ` and `IsAdmissible A.ρ`.
- every actual representation `S : Rep.{uW} ℂ (C.Levi F.Carrier)` of the
  product Levi that is a subquotient of the normalized opposite Jacquet
  module of `A`. Concretely, there are an actual invariant subspace
  `U : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ`
  and an intertwiner `q : U.toRepresentation.IntertwiningMap S.ρ` with
  `Function.Surjective q`. `Subrepresentation` and
  `Representation.IntertwiningMap` are the Mathlib declarations.
- every refinement `D : Geometric.BlockRefinement C`, that is, a block shape
  `D i` of each block size `C.size i`. The unrefined case is included.
- every character `ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ` of
  the flattened block-scalar tuples, and every complex-linear functional
  `φ : Module.Dual ℂ (Geometric.RefinedOppositeJacquetModule C D S.ρ)` on the
  full algebraic dual of the refined opposite Jacquet module of `S`.

The remaining hypotheses are

1. `IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ))`, for the
   product topology of the unit-group topologies from `T.topology`;
2. `φ ≠ 0`;
3. for every tuple `a` and every vector `v : S`,

   ```lean
   φ (T.normalizedRefinedOppositeJacquet C D S.ρ
       (flattenedLeviEquiv F.Carrier C D
         ((C.flatten D).blockScalarLevi F.Carrier a))
       (refinedOppositeJacquetMk C D S.ρ v)) =
     (ψ a : ℂ) * φ (refinedOppositeJacquetMk C D S.ρ v)
   ```

   Since `refinedOppositeJacquetMk` is surjective
   (`refinedOppositeJacquetMk_surjective`), this says that `φ` is an
   eigenvector of the transpose action of the flattened block scalars, with
   character `ψ` and power one.

The conclusion is `T.IsDualJacquetExponent (C.flatten D) A ψ`. It concerns
the same character `ψ`, not its inverse or complex conjugate. By its
definition in `Langlands.Representation.Exponents.DualJacquet`, the
conclusion means that `ψ` has open kernel and that

```lean
commutativeCharacterSpace (T.splitCentreDualJacquet (C.flatten D) A).ρ ψ 1 ≠ ⊥
```

So there is a nonzero functional `Φ` on the normalized opposite Jacquet
module of `A` for the flattened shape with
`Φ (r(blockScalarLevi a) x) = ψ(a) Φ(x)` for every tuple `a` and every `x`.
The transpose is `commutativeTranspose`, so `(a · Φ)(x) = Φ(a · x)`. The
hypothesis on `φ` has the same orientation.

The hypotheses do not include irreducibility, admissibility, smoothness,
unitarity, a central character, a tensor-product decomposition, finite
dimension or finite length of `S`. Nor do they ask for a scalar action of
any part of the centre on `S`. The relation between `S` and `A` is the
existential subspace-and-surjection relation above. It is not replaced by a
quotient of the whole Jacquet module. The functional `φ` lives on the actual
algebraic dual of the refined Jacquet module of `S`. No hypothesis says that
an eigenfunctional extends from a subspace.

## Actual constructions and normalization

`CuspidalJacquetMultiplicity.oppositeJacquet T C A` (module
`Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`)
is the actual coinvariant quotient of `A` by the lower block unipotent
subgroup `C.oppositeUnipotentSubgroup F.Carrier`. The block-diagonal Levi
acts through `C.leviEquiv`. The action is `Jacquet.normalizedActionOfModulus`
with the inverse `δ⁻¹` of the upper modulus `δ = T.leviModulus C`. Hence the
Levi element `m` acts on classes by `δ(m)^(1/2) [A(m) v]`.
`splitCentreOppositeJacquet_mk` records this formula with
`T.leviHalfModulus`, which is the positive half of the upper modulus.

`Geometric.RefinedOppositeJacquetModule C D S.ρ` (module
`Langlands.Representation.Parabolic.OppositeRefinementFunctors`) is the
actual coinvariant quotient of `S` by `refinedOppositeUnipotent F.Carrier C D`.
This is the product over the blocks `i` of the lower unipotent subgroups of
the shapes `D i`. The map `refinedOppositeJacquetMk C D S.ρ` is its quotient
map. `T.normalizedRefinedOppositeJacquet C D S.ρ` is the representation of
the common refined Levi `Geometric.refinedLevi F.Carrier C D` by the
radical normalizer, twisted by the inverse half of
`T.refinedOppositeLeviModulus C D`. That full opposite modulus is the
inverse of `T.refinedLeviModulus C D`. By
`inverseHalf_refinedOppositeLeviModulus` the twist equals the positive upper
half `T.refinedLeviHalfModulus C D`, so `normalizedRefinedOppositeJacquet_mk`
gives

```
m · [v] = δ_D(m)^(1/2) [S(m) v].
```

Both opposite normalizations are therefore the positive half of the
corresponding upper modulus. For the opposite parabolic `P̄ = M Ū` this is
`δ_P̄^(-1/2)`, which is Waldspurger's normalization `δ_Q^(-1/2)` of the
Jacquet module for the parabolic `Q = P̄`.

`flattenedLeviEquiv F.Carrier C D : (C.flatten D).Levi F.Carrier ≃*
Geometric.refinedLevi F.Carrier C D` (module
`Langlands.Representation.Geometric.FlattenedLevi`) is the existing
multiplicative equivalence. It reorders the flattened blocks into the nested
blocks `(i, j)` through `C.flattenBlockEquiv D`.
`(C.flatten D).blockScalarLevi F.Carrier a` is the block-scalar element
`(a_k · 1)_k` of the flattened product Levi.
`T.splitCentreDualJacquet (C.flatten D) A` is the transpose action of these
block scalars on the full algebraic dual of
`CuspidalJacquetMultiplicity.oppositeJacquet T (C.flatten D) A`.

The statement uses all of these constructions unchanged. It introduces no
replacement carrier, modulus, normalization or dual.

## Provenance

This is an internal algebraic decomposition interface. Worker 84 isolated
it as the common algebraic prerequisite of the analytic theorem task
`87151bf2-de30-4cd5-8569-2a8b3b3da96f` (target
`Langlands.GLTemperedJacquetClassExponentStatement`) and of Worker 363's
arbitrary scalar-layer temperedness task
`d5e74c40-0ddb-431d-aa97-8d5abfe2241a`.

Its source motivation is the proof of Lemma III.3.1 in Waldspurger, *La
formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), registered as `waldspurger-2003-plancherel`,
section III.3, printed p.267. There `π` is admissible and tempered, `P = MU`
is semi-standard and `V^w_P` is the sum of the generalized components of
`V_P` whose exponents have real part zero. The proof reads: "Soit
`P_M = M'U_M` un sous-groupe parabolique semi-standard de `M` et
`χ ∈ Exp((π^w_P)_{P_M})`. Posons `P' = P_M U`. Alors `χ ∈ Exp(π_{P'})`."
Section I.3, printed p.243, defines `Exp(π)` for admissible `π` as the
characters of `A_G` with a nonzero generalized eigenspace. It also
normalizes `π_P(m) j_P(v) = δ_P(m)^(-1/2) j_P(π(m) v)`.

This statement differs from the source in the following project choices.

- The parabolic `P` is the standard opposite block parabolic of `C`, and
  `P_M` is the product of the standard opposite block parabolics of the
  shapes `D i`. The composed parabolic `P' = P_M U` is the standard opposite
  parabolic of the flattened shape `C.flatten D`.
- The source applies the step to the direct summand `V^w_P`. Here `S` is an
  arbitrary actual subquotient of the whole normalized opposite Jacquet
  module. No real-part, temperedness or summand condition is imposed.
- Exponents are recorded as eigencharacters on full algebraic duals, as in
  `T.IsDualJacquetExponent`. The hypothesis is a nonzero eigenfunctional on
  the refined Jacquet module of `S`. It is not a generalized eigenvector.
- Exponents are characters of the flattened block-scalar tuples. These are
  the split centre of the flattened product Levi, which for `GL_n` block
  Levis is the group `A_{M'}` of the source.
- The three universes are independent.

The source states the step as evident. A proof of this statement must
supply the argument through an arbitrary subquotient. An eigenfunctional on
a subspace does not in general extend equivariantly to the whole space, so
a restriction argument alone does not suffice.

## Proof obligations

A later proof must establish the following, either directly or from
accepted Library proofs. It may not add any of them as a hypothesis of this
closed statement. Published proposition definitions, citations and pending
tasks are not proof evidence.

1. Exactness. Apply the refined opposite functor for `D` to the inclusion
   `U → O`, where `O` is the normalized opposite Jacquet module of `A`, and
   to the surjection `q : U → S`. The refined module of `U` must map
   injectively to that of `O`, and onto that of `S`. The injection needs the
   smoothness of `O`. The Library proofs
   `Langlands.Parabolic.normalizedRefinedOppositeJacquetExactness`
   (`Langlands.Representation.Parabolic.OppositeRefinementExactnessProof`) and
   `Langlands.Parabolic.standardOppositeJacquetAdmissibility`
   (`Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof`)
   are possible sources.
2. Transitivity and flattening. The refined opposite Jacquet module of `O`,
   pulled back along `flattenedLeviEquiv`, must be identified equivariantly
   with the normalized opposite Jacquet module of `A` for `C.flatten D`,
   compatibly with the quotient maps. Possible sources are
   `Langlands.Parabolic.normalizedOppositeRefinementTransitivity` and
   `Langlands.Parabolic.flattenedOppositeJacquetComparison`, which include
   the normalizations.
3. Transfer of the eigenfunctional. Steps 1 and 2 make the refined module of
   `S` a quotient of an invariant subspace `U'` of the flattened opposite
   Jacquet module of `A`, for the action of the flattened block scalars.
   Composing `φ` with this quotient map gives a nonzero functional on `U'`
   with the eigenequation for `ψ`.
4. Valid finite central-spectrum inheritance. The generalized components of
   the dual exponents of `A` for `C.flatten D` span the full algebraic dual.
   A nonzero functional with character `ψ` on an invariant subspace must then
   force `ψ` to be a dual exponent of `A`. The Library proofs
   `Langlands.glDualJacquetFiniteness`
   (`Langlands.Representation.Exponents.DualJacquetFinitenessProof`) and
   `Langlands.scalarSubquotientDualSpectrum`
   (`Langlands.Representation.Exponents.ScalarSubquotientDualSpectrumProof`)
   are possible sources. The latter takes the one-dimensional quotient
   `U' → ℂ` given by the functional. The open-kernel conjunct of the
   conclusion is hypothesis 1.

## Scope and boundaries

The statement contains no analytic inequality, unitarity, real-part,
temperedness or weak-exponent conclusion. Its consumers must prove their
analytic estimates and criteria separately. It does not state the converse
inclusion, multiplicities, nilpotence orders or finiteness of the dual
spectrum of `S`. It concerns the opposite Jacquet modules and does not by
itself produce a witness of `T.IsJacquetExponent` for the upper Jacquet
module.
