# Sufficiency in Casselman's criterion from the strict-chamber statement

Author: Worker 4712. Module
`Langlands.Representation.Exponents.CasselmanSufficiencyReduction`.

This module states the sufficiency half of Casselman's criterion (Renard 2026,
VII.1.2, printed p.221 / PDF p.227) in the formulation of the published
`Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicCasselmanCriterionStatement`.
It reduces that half to the published Bruhat–Tits statement
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`.
Along the way it proves the one remaining structural input of the published
sufficiency assembly, the selected-root valuation law. It proves neither the joint
special-compact statement nor sufficiency itself. The necessity half is proved
separately (`CasselmanNecessity.md`).

## The sufficiency statement

`RepresentedParabolic.ArbitraryParabolicCasselmanSufficiencyStatement : Prop`
(universes `u` for the field, `v` for the carrier) has exactly the binders of
`ArbitraryParabolicCasselmanCriterionStatement`: a Hausdorff nonarchimedean local
field, a connected reductive `G` with the published point topology assumed locally
compact and nonarchimedean, a Borel Haar measure on `G(k) ⧸ Z(G(k))`, and
`π : SmoothRep.{0, u, v}` with `π.IsAdmissible` and a unitary central character.
It replaces that statement's biconditional by its right-to-left implication. If, for
all represented parabolic data `p, l, r, a`, every compatible presentation `pres`
and every normalized Jacquet exponent `χ`, the real part `normalizedRealPart χ`
lies in `pres.positiveCone`, then `IsSquareIntegrableModCenter π.representation haar`.
The right-hand condition is copied verbatim from the criterion statement. This is
the "si" part of Renard's "π est de carré intégrable modulo le centre si et
seulement si … `ℜ(χ) ∈ ^G_P[𝔞*_M]^+`". The root cone and the `q^(-s)` real part are
the published choices, documented in `ArbitraryParabolicCasselmanStatement.md`.

## The selected-root valuation law

`RationalPointFamily.HasSelectedRootValuationLaw i ν : Prop`, for a torus map
`i : T ⟶ G` over a nonarchimedean local field `k` and a cocharacter `ν`, says the
following. For every finite set `I` of simple relative roots, every torus point
`t ∈ T(k)`, and every central element `z` of the standard Levi points `levi i ν I`
with `z = i(t)`, every `α ∈ I` satisfies `v(simpleRootPointValue i ν α t) = 1`,
that is, `|α(t)| = 1`.

This is verbatim the hypothesis `hselected` of the published
`squareIntegrableModCenter_of_positiveRepresented`
(`CasselmanSufficiencyAssembly.lean`) and of
`strictStandardExponents_of_positiveRepresented`, packaged as a proposition. In
Renard's notation it says that the simple roots of the Levi `M` have absolute value
one at every torus point central in `M`.

## Results

Namespace `Langlands.Aubert.General.RationalPointFamily`:

- `map_cocharacterPoints`: `i(c(t)) = cocharPoint (c ≫ i) t` for a cocharacter
  `c` of `T` and `t ∈ kˣ`.
- `latticePairing_nonpos_of_commute_rootPoint`. Let `T` be split and `x ≠ 1` a
  rational point of the root subgroup `U_α` (`RelativeRoot.subgroup i α`). Let
  `t ∈ T(k)` be such that `i(t)` commutes with `x`, and let `c` be a cocharacter
  with `t · c(ϖ)⁻¹` in the norm kernel `T(k)¹`
  (`Plancherel.rationalCommonNormKernel`). Then `⟨α, c⟩ ≤ 0`.
- `simpleRootPointValue_valuation_eq_one_of_leviCenter`: for `G` connected
  reductive and `i` a maximal split torus, the conclusion of the law for one
  `I, t, z, α`.
- `HasSelectedRootValuationLaw`, `hasSelectedRootValuationLaw`: the definition
  above, and the theorem that it holds for every maximal split torus of a
  connected reductive group, for every `ν`.

Namespace `Langlands.Aubert.General.RepresentedParabolic`:

- `arbitraryParabolicCasselmanSufficiency_of_strictJacquet`:
  `RationalStrictJacquetSquareIntegrabilityStatement.{u, v} →
  ArbitraryParabolicCasselmanSufficiencyStatement.{u, v}`.
- `arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis`:
  `JointSpecialCompactBasisExistenceStatement.{u} →
  ArbitraryParabolicCasselmanSufficiencyStatement.{u, v}`.

## Proofs

`latticePairing_nonpos_of_commute_rootPoint`. Suppose `⟨α, c⟩ > 0`. Give `G(k)`
and `T(k)` the published point topology; `G(k)` is a Hausdorff topological group
(`rationalPoint_isTopologicalGroup`, `rationalPoint_t2Space`). The norm kernel
`K⁰ = T(k)¹` is compact (`isCompact_commonNormKernel`), and the point map of `i`
is continuous (`continuous_rationalPointMap`). Hence
`C = {i(s) x i(s)⁻¹ | s ∈ K⁰}` is compact, hence closed. It does not contain `1`,
because `x ≠ 1`. Since `⟨α, c⟩ > 0`, the published
`RelativeRoot.subgroup_le_dynamicUnipotent` puts `x` in the dynamic radical
`U(c ≫ i)(k)`. The published `eventually_cocharPoint_pow_conj_mem_ambient`, with
`ϖⁿ → 0`, gives `n` with `b^n x b^{-n} ∉ C`, where
`b = cocharPoint (c ≫ i) ϖ = i(c(ϖ))`. Put `s₀ = t · c(ϖ)⁻¹ ∈ K⁰`. Since `T` is
commutative, `c(ϖ) = s₀⁻¹ t`, so `bⁿ = i(s₀⁻ⁿ) i(t)ⁿ`. Conjugation by `i(t)ⁿ`
fixes `x`, so `bⁿ x b⁻ⁿ = i(s₀⁻ⁿ) x i(s₀⁻ⁿ)⁻¹ ∈ C` because `s₀⁻ⁿ ∈ K⁰`. This
is a contradiction.

`simpleRootPointValue_valuation_eq_one_of_leviCenter`. The published
`RelativeRoot.exists_rootPoint_actual` gives `x ≠ 1` in `U_α(k)`. For every
standard cocharacter `ζ` of `I`, `⟨α, ζ⟩ = 0`, so `U_α ≤ Z(ζ ≫ i)` (published
`RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero`). Hence
`x ∈ levi i ν I` (`mem_levi_iff`), and `i(t) = z` commutes with `x`. The published
`isUniformizerLatticeSection` writes `t = s₀ · c(ϖ)` with `s₀ ∈ T(k)¹`. The
previous lemma, applied to `(t, c)` and to `(t⁻¹, -c)` (note
`t⁻¹ · (-c)(ϖ)⁻¹ = s₀⁻¹`), gives `⟨α, c⟩ ≤ 0` and `-⟨α, c⟩ ≤ 0`, so
`⟨α, c⟩ = 0`. The integer valuation of `α(t)` is the sum of that of `α(s₀)`, which
is `0` (`mem_rationalCommonNormKernel_iff_valuation`), and that of `α(c(ϖ))`, which
is `⟨α, c⟩ = 0` (`isUniformizerLatticeSection`). The published
`rationalCharacterValuation_nonneg_iff` and `rationalCharacterValuation_pos_iff`
turn order `0` into valuation `1`.

`arbitraryParabolicCasselmanSufficiency_of_strictJacquet`. Fix the data of the
statement, an admissible `π` with a unitary central character, and the cone
condition. Apply the published `squareIntegrableModCenter_of_positiveRepresented`
with:

- a maximal split torus `i` and a generic `ν` from
  `exists_maximalSplitTorus_genericCocharacter`;
- the proved `standardCocharacter`;
- closedness of the standard radicals from
  `isClosed_unipotent_of_isNonarchimedeanLocalField`;
- the standard presentations `standardCasselmanPresentationOfGeometry`, built
  from `genericMinimalParabolic` and the geometric properties
  `standard_representatives_geometric_of_standardCocharacter`;
- the selected-root law `hasSelectedRootValuationLaw`;
- the hypothesis `hsq`.

`arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis` composes this
with the published reduction `rationalStrictJacquetSquareIntegrabilityReduction`.

## Scope and provenance

The sufficiency statement has source provenance: it is the "if" half of Renard
VII.1.2, with the binders and cone condition of the published criterion statement.
`HasSelectedRootValuationLaw` is an internal packaging (provenance: derived) of
the published assembly's `hselected` hypothesis. It is needed to identify the tests of the strict
statement with the cone condition at standard parabolics. Renard's proof of VII.1.2
(printed p.222 / PDF p.228) takes the chamber basis `t_α` with `|α(t_α)| < 1` and
`|β(t_α)| = 1` for `β ≠ α` from V.3.24 and does not state this law separately. The
Lean proof is internal: it uses the contraction of root subgroups, not Weyl-group
data.

Together with the necessity theorem, this module leaves exactly one unproved
statement between the Library and the criterion:
`JointSpecialCompactBasisExistenceStatement` (Task 4169). It supplies the special
compact subgroup, the Iwasawa and Cartan decompositions and the simultaneous
Iwahori bases that Renard uses in the sufficiency half (V.5.1, VII.1.2). Source:
David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`; PDF
page = printed page + 6).
