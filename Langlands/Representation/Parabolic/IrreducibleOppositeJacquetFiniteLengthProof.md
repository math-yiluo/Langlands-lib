# Finite length of actual opposite Jacquet modules

Author: Worker 319.

`Langlands.Parabolic.irreducibleOppositeJacquetFiniteLength.{uF,uV}`
proves the unchanged Library proposition
`Langlands.Parabolic.IrreducibleOppositeJacquetFiniteLengthStatement.{uF,uV}`.
For every prime, actual p-adic field, supplied compatible topological data,
positive rank and block shape, the actual opposite normalized Jacquet
representation of irreducible admissible complex input has finite length
over the complex group algebra of the actual product Levi. The field and
carrier universes remain independent. The opposite quotient can be zero.

The proof imports the target pair unchanged. Its two mathematical inputs are
the published `Parabolic.normalizedJacquetFiniteLength` in
`Representation.Classification.FiniteLengthProof` and the general
`OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv` in
`Representation.Classification.OppositeCuspidalJacquetFiltrationProof`.
Although the latter module also proves a conditional filtration theorem,
this equivalence is constructed for every ambient `Rep A`; it assumes no
filtration theorem, smoothness, irreducibility or finite length.

## Derived ambient finite generation

The elementary helper
`IrreducibleOppositeJacquetFiniteLength.finite_asModule_of_irreducible`
works over any field and acting monoid. Mathlib's
`Representation.irreducible_iff_isSimpleModule_asModule` makes the associated
group-algebra module simple. It is therefore nontrivial. Choose a nonzero
vector `v`. The map

```text
LinearMap.toSpanSingleton k[G] π.asModule v : k[G] →ₗ[k[G]] π.asModule
```

is surjective by `IsSimpleModule.toSpanSingleton_surjective`: the span of a
nonzero vector in a simple module is the whole module. The regular module
`k[G]` is finitely generated over itself, so
`Module.Finite.of_surjective` gives ambient finite generation. This is
group-algebra finite generation, with no claim of finite dimension over
the coefficient field.

## The constructed opposite comparison and its orientation

Write `w = B.reverseMatrix F.Carrier` and
`θ = OppositeCuspidalJacquetFiltration.leviReverseEquiv B`. The latter is the
actual group equivalence

```text
θ : B.Levi F.Carrier ≃* B.reverse.Levi F.Carrier,
θ(m)(i) = m(i.rev).
```

The imported `oppositeJacquetReverseEquiv T B (Rep.of π)` is a representation
equivalence from

```text
(T.normalizedJacquet B.reverse π).comp θ.toMonoidHom
```

to exactly

```text
(CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of π)).ρ.
```

The comparison is proved in its imported module as follows.

1. Conjugation by `w` carries the reversed upper unipotent subgroup onto
   the opposite unipotent subgroup. Two `Jacquet.lift` constructions descend
   `π(w)` and `π(w⁻¹)` to inverse linear maps on the actual ambient
   coinvariants. Their inverse laws follow on vector representatives from
   the representation identities.
2. `B.reverse.jacquetModuleEquiv π`, constructed in `Jacquet.Parabolic`,
   identifies the upper parabolic-restricted quotient with the ambient
   upper-subgroup quotient. This identification itself uses quotient lifts
   in both directions, not definitional equality of the two carriers.
   Composing these equivalences sends the upper class of `v` to the
   opposite class of `π(w)v`.
3. The matrix identity
   `w * emb_reverse(θ(m)) * w⁻¹ = emb_B(m)` identifies the Levi actions.
   The proved determinant-product identity `T.leviModulus_reverse` gives
   `δ_reverse(θ(m)) = δ_B(m)⁻¹`. Thus the inverse square root used by the
   reversed upper normalized action is the inverse square root of
   `δ_B(m)⁻¹`, namely the positive upper half-modulus.

That last factor is precisely the normalization of the existing opposite
action: its `normalizedActionOfModulus` receives the inverse transported
upper full modulus. On classes its action is

```text
m · [v] = δ_B(m)^(1/2) [π(emb_B(m))v].
```

The imported proof checks equivariance on representatives using the actual
full-modulus formulas. It neither replaces the opposite radical by the upper
radical nor assumes a comparison as an additional premise. Whole-block
reversal preserves within-block positions; its matrix need not be an
involution. The two quotient maps use `w` and `w⁻¹` separately.

## Finite-length transport and exact closure

The helper `Parabolic.oppositeJacquetFiniteLength` takes an admissible ambient
representation together with its group-algebra finite generation. Apply the
published upper theorem to `B.reverse`. This gives finite length of
`T.normalizedJacquet B.reverse π`. Since `θ` is surjective,
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` gives finite length
of its pullback along `θ`. Finally,
`FiniteLengthAssembly.finiteLength_of_surjective` applies to the surjective
intertwiner underlying the constructed representation equivalence and gives
finite length of the actual opposite action.

This helper permits every rank, including zero, and zero carriers. The closing
theorem retains exactly the target's positive-rank quantifier, applies this
helper and discharges its finite-generation input by the cyclicity argument.
The closing theorem has the complete unapplied type
`IrreducibleOppositeJacquetFiniteLengthStatement.{uF,uV}`. It adds no
finite-generation, finite-length, scalar-central-character, temperedness,
unitarity, finite-dimensionality or comparison hypothesis.

## Provenance and dependency boundary

This is a derived algebraic assembly of published Library proofs, not a
transcription of a stronger source theorem. The unchanged statement Markdown
records Casselman 1995, §1.4 p.13, Proposition 3.2.1 p.33,
Theorem 3.3.1 p.35 and Theorem 6.3.10 pp.60–61, and Silberger 1979,
Theorem 5.4.1.6 pp.291–292. The upper finite-length proof's Markdown describes
its implemented decomposition and induction on proper refined Jacquet
modules. The reversal equivalence and its quotient and modulus calculations
are internal constructions from the published matrix, Jacquet and induction
interfaces. Cyclicity and finite-length transport are elementary module
arguments implemented using Mathlib and the published assembly lemmas.

The comparison helper has no dependency on its module's final conditional
filtration theorem. No upper associated-filtration theorem is assumed or
applied here. The import closure contains none of the consuming
discrete-series opposite Jacquet criterion, its summand proof, regular
Langlands heads or exhaustion, square-integrable Langlands classification,
or downstream induced finite-type or finite-length proofs. The target pair
and its import closure remain unchanged.
