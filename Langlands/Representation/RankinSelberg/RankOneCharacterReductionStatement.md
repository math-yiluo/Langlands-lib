# Reduction of full rank-one Whittaker type to a quasicharacter

`Langlands.RankinSelberg.RankOneCharacterReductionStatement.{uF,uV}` is a
closed Prop-valued statement. It quantifies over every prime `p`, every
`PadicField.{uF} p`, every `UnitaryAdditiveCharacter` for its canonical topology,
every `V : Type uV` with `AddCommGroup V` and `Module ℂ V`, and every actual
representation of `Langlands.GeneralLinear (0 + 1) F.Carrier` on `V`.
The field and carrier universes are independent.

Its sole representation premise is the published full predicate
`IsOfWhittakerType 0 (standardCharacter ψ 0) π`, using the canonical field
topology. This predicate includes admissibility, finite generation over the
actual group algebra, and a complex linear equivalence between the entire
standard Whittaker-functional space and the complex scalars. Smoothness is
included in admissibility. No irreducibility, finite-dimensionality, nonzero
vector, chosen carrier equivalence, continuity of an unbundled action, or
analytic factor certificate is an additional premise.

The conclusion is the existence of
`χ : HarmonicAnalysis.Quasicharacter F.Carrier` and
`Nonempty (π.Equiv (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)))`.
Here `Quasicharacter` is the published abbreviation for a continuous monoid
homomorphism from the field's units to the complex units.
The target is exactly the published scalar representation on `ℂ`, whose
action is `χ` composed with the GL(1) determinant.
The equivalence is an actual `Representation.Equiv`: it is complex linear,
bijective and intertwines the GL(1) actions. Its orientation is from the
arbitrary carrier representation to the scalar representation. The statement
does not substitute a mere equivalence of carriers or the weaker existence
of a Whittaker functional.

The provenance is internal and derived from the published definitions in
`Langlands.HarmonicAnalysis.Basic`,
`Langlands.Representation.RankinSelberg.LocalFactor`,
`Langlands.Representation.RankinSelberg.AnalyticStatement` and
`Langlands.Representation.Whittaker.GeneralLinear`.
It is not a transcription of a separately numbered literature result.
The following elementary route explains the intended justification and the
obligations for a separate proof contribution:

1. The published `Whittaker.glFunctionals_rankOne` identifies the rank-one
   functional submodule with the whole algebraic dual, since the upper
   unipotent group is trivial. The full Whittaker-type premise therefore
   identifies the entire algebraic dual with `ℂ`.
2. This scalar dimension forces the carrier itself to be one-dimensional
   and nonzero. One can justify the dimension bound using separation of
   vectors by algebraic linear forms, or the injection into the double
   dual. The nonzero dual excludes the zero carrier. These steps must
   work for the arbitrary universe `uV`.
3. Choose a complex linear equivalence from the carrier to `ℂ`. Conjugating
   the given GL(1) action yields nonzero scalar multipliers. The determinant
   identification of GL(1) with the field's units turns these multipliers
   into a multiplicative character and gives the required intertwining
   equivalence with `rankOneCharacter`.
4. Smoothness, extracted from admissibility, supplies an open subgroup
   fixing a nonzero vector. In a one-dimensional representation this
   subgroup acts trivially. The topological determinant identification
   then gives an open kernel for the character on the field's units.
   It follows that the character is locally constant and hence continuous,
   giving the required bundled `Quasicharacter`.

This file implements only the statement, not these arguments. Compilation
checks the proposition and its types; it does not establish the proposition.
The opposite direction, from an actual continuous scalar quasicharacter to
full Whittaker type, is the separate `RankOneWhittakerTypeStatement`.
The reduction here makes no JPSS multiplicativity, Godement–Jacquet comparison,
L-factor or gamma-factor existence, or Section 7 assertion.
