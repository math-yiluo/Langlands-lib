# Scalar generalized characters and normalized Jacquet scalar compatibility

Authors: Worker 561 (draft) and Worker 846 (revision).

This module contains two Prop-valued definitions and proves neither of them.
Both are internal elementary algebra about published representations. They
are not quoted from the literature; the provenance is explained below.

## The predicates

For a complex representation `π` of a monoid `A` and a character
`χ : A →* ℂˣ`, the published predicate `IsGeneralizedEigencharacter π χ` from
`Langlands.Representation.Exponents.Jacquet` says that some
`characterSpace π χ k` is nonzero. By the published
`isGeneralizedEigencharacter_iff` this means: there are a natural number `k`
and a vector `v ≠ 0` with `((π a - χ(a) • 1)^k) v = 0` for every `a : A`. The
same power `k` serves every group element.

For a representation `ρ` of `G`, a homomorphism `z : C →* G` and a character
`ω : C →* ℂˣ`, the published predicate
`Classification.HasScalarCharacter ρ z ω` from
`Langlands.Representation.Classification.ConstituentRelations` says
`ρ (z c) v = ω(c) • v` for every `c : C` and every vector `v`. It is stated
for complex representations, so this module keeps the coefficient field `ℂ`.
`ρ.comp z` is the representation `c ↦ ρ (z c)` of `C`.

## Generic scalar detection

`Langlands.ScalarGeneralizedEigencharacterDetection.{uG,uC,uV}` has three
independent universe parameters. It is the conjunction of two clauses.

1. For all groups `G : Type uG` and `C : Type uC`, every
   `V : Type uV` with `AddCommGroup V` and `Module ℂ V`, every
   `ρ : Representation ℂ G V`, every `z : C →* G` and all characters
   `ω χ : C →* ℂˣ`: if `HasScalarCharacter ρ z ω` and
   `IsGeneralizedEigencharacter (ρ.comp z) χ`, then `χ = ω`.
2. With the same quantifiers and the additional hypothesis `Nontrivial V`:
   if `HasScalarCharacter ρ z ω`, then
   `IsGeneralizedEigencharacter (ρ.comp z) χ ↔ χ = ω`.

The first clause has no nontriviality hypothesis: the generalized-character
premise already supplies a nonzero vector. It covers every power `k`. For
`k = 0` the premise says `v = 0` for a vector `v ≠ 0`, so that case holds
vacuously. Neither clause assumes that `z` lands in the centre of `G`; the
prescribed scalar action is the only hypothesis. There is also no
commutativity, finite dimension, finite length, admissibility, continuity,
open-kernel or ordinary-eigenvector hypothesis.

Intended derivation, which this module does not carry out: by scalar action,
`ρ (z c) - χ(c) • 1 = (ω(c) - χ(c)) • 1`. The common-power equation becomes
`(ω(c) - χ(c))^k • v = 0`. Since `v ≠ 0` over the field `ℂ`, the power
`(ω(c) - χ(c))^k` is zero, hence `ω(c) = χ(c)` for every `c`. For the
reverse implication of the second clause, scalar action makes any nonzero
vector an ordinary eigenvector for `ω`, and the published
`isGeneralizedEigencharacter_of_eigenvector` then applies.

## Actual normalized Jacquet modules

`Langlands.PadicField.TopologicalData.NormalizedJacquetScalarCompatibility.{uF,uV} T`
has independent field and carrier universes. Its parameters are a prime `p`
(with `Fact p.Prime`), an actual `F : PadicField.{uF} p` and a realization
`T : F.TopologicalData`, so the proposition is stated for every such `T`. It
quantifies every `n : ℕ`, every block shape `B : GeneralLinear.BlockShape n`,
every `V : Type uV` with `AddCommGroup V` and `Module ℂ V`, every complex
representation `ρ` of `GeneralLinear n F.Carrier` on `V`, and every
`ω : F.Carrierˣ →* ℂˣ`. It assumes
`HasScalarCharacter ρ GeneralLinear.scalar ω`, where `GeneralLinear.scalar`
sends a unit `a` to the scalar matrix `a · 1`. It concludes both:

1. `HasScalarCharacter (T.normalizedJacquet B ρ) (B.scalarLevi F.Carrier) ω`.
2. Every `χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` with
   `IsGeneralizedEigencharacter (T.splitCentreJacquet B ρ) χ` satisfies
   `χ.comp (Pi.constMonoidHom (Fin B.length) F.Carrierˣ) = ω`.

Here `T.normalizedJacquet B ρ` is the published normalized Jacquet module of
`Langlands.Representation.Jacquet.Parabolic`, on the actual coinvariant
quotient `B.JacquetModule ρ`. The published
`GeneralLinear.BlockShape.scalarLevi B R` from
`Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof`
is `(B.blockScalarLevi R).comp (Pi.constMonoidHom _ _)`: it sends `a` to the
constant block scalar `(a · 1, …, a · 1)`. It is not the full split centre.
The published `T.splitCentreJacquet B ρ` is
`(T.normalizedJacquet B ρ).comp (B.blockScalarLevi F.Carrier)`. The second
clause concerns every character `χ`, without the open-kernel condition of
`T.IsJacquetExponent`, so it applies in particular to every Jacquet exponent.

This states compatibility with the diagonal copy of the ambient centre only.
It identifies no character of an individual block, and it does not identify
the Jacquet module with a tensor product. There is no smoothness,
finite-dimensionality, nontriviality, admissibility or finite-length
hypothesis. Zero Jacquet modules are included: there the first clause is
automatic and the premise of the second clause cannot hold.

Intended derivation, which this module does not carry out: the quotient map
is surjective (`GeneralLinear.BlockShape.jacquetMk_surjective`), so the first
clause can be checked on quotient classes. On a class, the formula
`PadicField.TopologicalData.normalizedJacquet_mk` gives the inverse square
root of `T.leviModulus B` times the class of the action of the embedded Levi
element. `GeneralLinear.BlockShape.leviEmbedding_scalarLevi` identifies the
embedded constant block scalar with `GeneralLinear.scalar a`, and
`PadicField.TopologicalData.leviModulus_scalar` shows that the modulus is one
there. The quotient action therefore retains `ω`. For the second clause,
`(T.splitCentreJacquet B ρ).comp (Pi.constMonoidHom _ _)` is the action of
`T.normalizedJacquet B ρ` along `B.scalarLevi F.Carrier`. Restricting the
common-power equations, with the same vector and power, to constant
coordinates gives a generalized character `χ.comp (Pi.constMonoidHom _ _)`
of that action. Generic scalar detection and the first clause identify it
with `ω`.

## Imports and independence

The module imports `Langlands.Representation.Exponents.Jacquet`, for the
generalized-character predicate and `T.splitCentreJacquet`, and
`Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof`,
for `B.scalarLevi` and `leviEmbedding_scalarLevi`. The latter is an internal
calculation of scalar actions on segment inductions. The transitive Library
imports of this module concern groups, local fields, smooth representations,
twists, inductions and Jacquet modules. They contain no square-integrability,
Casselman criterion, derivative theorem, exhaustion, tempered-block
uniqueness, ordered-head, quotient-coverage or Langlands-classification
result.
