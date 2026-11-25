# Strict monotonicity of the nonjuxtaposed highest derivative

This module proves item (e), exactly the published proposition
`Langlands.Classification.NonjuxtaposedSegmentSocleDerivativeStrictMono`
from `Langlands.Representation.Classification.SegmentSocleDerivativesStatement`.
Its main theorem is

```lean
theorem Langlands.Classification.nonjuxtaposedSegmentSocleDerivativeStrictMono
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NonjuxtaposedSegmentSocleDerivativeStrictMono.{uF, uV} F T
```

It adds no theorem-valued premise. For every supplied nontrivial unitary
additive character, every ordered product datum of supplied segment socles
with no juxtaposition between distinct positions, and every free bounded
order equal to the sum of the segment ranks, strict inclusion of two
subrepresentations implies strict inclusion of the actual derivative maps'
ranges inside the derivative of that same induced product. Repeated equal
segments and every ordering are retained. Product irreducibility is not a
hypothesis.

## Original sources and provenance

The governing original is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)* (1980),
registered as `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The relevant passages are Proposition 4.3 and its use in the proof of
Theorem 4.2, printed p.184, and Proposition 4.6(3), pp.185–186. These are
zero-based PDF indices 20–22 in the retained registered original. The
source uses the constituent-level assertion to obtain strictness of the
highest derivative on subrepresentations. The Lean proof takes an
irreducible quotient of the nonzero finite-length representation `K₂/K₁`;
that quotient is an actual subquotient of the original product.

The exactness input comes from I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), registered
as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Proposition 3.2(a), printed p.451, gives exactness of the minus functors;
§3.5, p.452, and §4.3, p.454, define the iterated and general-linear
derivatives. These are zero-based PDF indices 11, 12 and 14. The retained
original passages, including the adjacent Leibniz statements on p.455,
were read. The original files' fingerprints agree with the registered
values. No `notes/errata/<source-id>.md` for either source was present in
the supplied workspace, project or current Library locations checked.

The quotient construction, coatom extraction, exact-functor range comparison,
and group-algebra finiteness adapters are internal proofs implementing that
lattice argument. They are not additional assertions attributed to the
source. The sources explain the mathematics; every mathematical input used
by Lean is a published theorem or an elementary lemma proved in this module.

## Parameters and normalization

The outer parameters are a prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p`, and the supplied `T : F.TopologicalData`.
Every instance uses `T.topology`. The theorem quantifies over every supplied
nontrivial continuous unitary additive character `ψ` and constructs none.
The level parameters are exactly `uF, uV`, in that order. The datum is
`d : T.SegmentProductDatum.{uV, uF} n`, with all actual smooth carriers in
`Type (max uF uV)`. The generic helpers preserve the common carrier universe
and allow independent source and target group universes.

The derivative is the unchanged published
`Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk`, with its
determinant inverse-half normalization. The local quotient argument and the
published derivative-exactness composition act directly on these functors.
The inherited constituent theorem (d) uses the independently published
`Langlands.mirabolicRadicalHaarModulus` comparison where its
segment and Leibniz inputs need the source's Haar-modulus convention;
see `Langlands.Group.GL.MirabolicModulusProof`. The present proof inherits that
comparison through (d), without introducing another normalization.

The order `k` is free, subject to `hk : k ≤ n` and
`k = ∑ i, (d.segments i).rank`. The ranges compared are those of the actual
maps on `SmoothRep.subtype d.induced K₁` and
`SmoothRep.subtype d.induced K₂`; both lie in the subrepresentation lattice
of the same derivative object. Rank zero and the empty product are included
by the one-dimensional rank-zero product argument below. Singleton and
repeated segments require no extra hypothesis.

## Implemented proof

The new helpers are in namespace `Langlands.Classification.NonjuxtaposedStrictMono`.
The injection and irreducible-quotient helpers retain their published names in
`Langlands.Aubert.ZelevinskyHighestDerivative` and
`Langlands.Classification.SegmentHeadSupport`, respectively, and are imported
from [FiniteLengthHelpers](../Category/FiniteLengthHelpers.md).

1. `hasFiniteLength_of_injective` and `hasFiniteLength_of_surjective` move
   finite length along an injective or surjective intertwiner. They use
   Mathlib's `IsFiniteLength.of_injective` / `of_surjective` on the group
   algebra module.
2. `exists_irreducible_quotient`: a nonzero finite-length smooth
   representation has an irreducible quotient. The proof takes a coatom of its
   Noetherian submodule lattice, quotients by it, and uses
   `isSimpleModule_iff_isCoatom`. This internal module-lattice argument
   assumes no segment classification or special-head criterion.
3. `inclusion A h` is the actual intertwiner `K₁ → K₂` for `h : K₁ ≤ K₂`.
   `inclusion_comp_subtype` (proved by `rfl`) states that composing it with
   the inclusion of `K₂` gives the inclusion of `K₁`.
4. `map_subtype_injective`: an exact functor (`MapsShortExactIntertwiners`)
   sends the inclusion of a subrepresentation to an injective map. Use the
   short exact sequence `K → A → A/K`.
5. `range_map_subtype_lt` is the generic step. Let `J` be an exact functor,
   `A` a finite-length representation, and suppose `J ω` is nonzero for every
   irreducible subquotient `ω` of `A`. Then `K₁ < K₂` implies
   `range (J (K₁ ↪ A)) < range (J (K₂ ↪ A))`. Monotonicity follows from the
   factorization `K₁ → K₂ → A`. Now suppose the two ranges were equal.
   Injectivity of `J (K₂ ↪ A)` would make `J (K₁ → K₂)` surjective, and
   exactness of `K₁ → K₂ → K₂/K₁` would then give `J (K₂/K₁) = 0`. But
   `K₂/K₁` is nonzero and has finite length, so it has an irreducible quotient
   `σ`. This `σ` is an irreducible subquotient of `A`, via
   `SmoothRep.isSubquotient_iff_exists`. Exactness makes `J σ` a quotient of
   `J (K₂/K₁)` (`LevelCalculus.map_surjective_of_exact`), so `J σ = 0`. That
   contradicts the hypothesis.
6. `isIrreducible_of_isSegmentSocle` extracts irreducibility from the supplied
   relation `T.IsSegmentSocle Δ π`.
7. `hasFiniteLength_induced`: `d.induced` has finite length when every factor
   is a supplied segment socle. For `n > 0` this is the published
   `Langlands.Classification.irreducibleProductFiniteLength.{uF, max uF uV}`
   applied to `d.shape`, `d.blocks` and step 6. For `n = 0`,
   the published `SegmentProductOrderedAssembly.finrank_zeroDatum` shows that
   the product is one-dimensional, hence Noetherian and Artinian.
8. The main theorem applies step 5 with
   `J = generalLinearDerivative T ψ n k hk`. Exactness is the published
   `Derivative.generalLinearDerivativeExactness.{uF, max uF uV} F T ψ n k hk`.
   Finite length comes from step 7. The nonvanishing hypothesis is the first
   conjunct of the published
   `nonjuxtaposedSegmentSocleConstituentLevel.{uF, uV} F T`, applied to the
   same `ψ`, `d`, segment-socle and nonjuxtaposition hypotheses and order `k`.
   The second conjunct of (d), vanishing in higher orders, is not used.

## Published inputs

The five direct imports are listed below. Module names are relative to
`Langlands.Representation`. Lean imports mathematics by module and
declaration name.

| Module and use | Publication commit |
| --- | --- |
| `Classification.SegmentSocleDerivativesStatement`, fixed target | `c76b7751d5e9d82df7a4e5d57684adcee5d41cb7` |
| `Classification.NonjuxtaposedSegmentSocleConstituentLevelProof`, first conjunct of (d) | `6820dc99b5972ed5761be21b4ac8afeba7584644` |
| `Classification.IrreducibleProductFiniteLengthProof`, positive-rank product length | `ddf3850e87ef10e9eabe230b50f772e4890d71bd` |
| `Classification.SegmentProductOrderedAssembly`, only `finrank_zeroDatum` | `7543113c99690e18b45f3b22d252e8cf77c3964e` |
| `Derivative.GeneralLinearDerivativeExactnessProof`, actual functor exactness | `2003a7a6a41b5e54c3f790e0887743ed616ed614` |

The required input (d) is the unconditional published theorem
`nonjuxtaposedSegmentSocleConstituentLevel`. The finite-length theorem is
`irreducibleProductFiniteLength`. The exactness theorem is
`Derivative.generalLinearDerivativeExactness`; its composition uses the
published minus-exactness proof. No conditional exactness or
constituent-level hypothesis remains in the final theorem.

The exactness module has its generic identity/composition laws in
`Derivative.ShortExactFunctorLaws`. Its Lean agrees with the cited
publication commit. The shared helper also contains
`LevelCalculus.map_surjective_of_exact`, extracted from `LevelCalculus`:
apply the exactness premise to the actual kernel inclusion and the supplied
surjection. It imports only the minus-exactness statement and actual
subquotient definitions, with no segment or classification input. This is
the generic lemma used in step 5; importing its public namespace does not
import the downstream `LevelCalculus` module. The finite-length, rank-zero
assembly and constituent-level pairs agree with their published versions.

## Direct and transitive independence

The module reuses the identical published quotient and injective finite-length
helpers through [FiniteLengthHelpers](../Category/FiniteLengthHelpers.md). Their
proofs and full published names are unchanged. This shared module imports only
`Category.Subquotients` and the complex numbers, both already in the audited
closure; it adds no classification or derivative input. The counts below record
the module before the helpers were extracted into that shared module.

At Library base `ca102a8a50473f5a0f03f7fcd16cd21d996a6f7d`, the five direct
imports close to 1,297 Langlands modules and 337 directly named external
import roots. This is exactly the published (d) module's import closure:
all four other direct imports already lie in it. Adding this final module
gives 1,298 project modules. Every project import resolves and has nonempty
paired Markdown. All 1,297 inherited Lean/Markdown pairs are unchanged from
that base. The full 114-module target closure, including its own pair, is
unchanged in both Lean and Markdown. The individual root closure sizes are
114 for the target, 477 for finite length, 180 for rank-zero assembly,
73 for exactness and 1,297 for (d).

The new quotient argument uses only actual morphisms, module finite length,
a coatom and short exact sequences. The new final application adds only
the permitted (d), product finite length, rank-zero product and exactness
inputs. The inherited (d) proof supplies its own
support-shift, ordered support-selection, finite-length extraction and
normalization audits. Since every inherited pair matches the current
Library and all other imports were already in (d)'s closure, the current
proof introduces no additional upstream mathematical dependency.

A comment-stripped scan of the full closure finds excluded identifiers
only as proposition definitions or their conjunctions in the fixed
statement chain. The permitted support-shift and constituent-level proofs,
and the present theorem's own name, also occur. This lexical scan is
supplemented by the implemented quotient proof and the inherited published
proof audits; no excluded statement is supplied as a theorem or premise.

Generic infrastructure originally published in the development of excluded
results is distinguished from their excluded conclusions. The inherited
single-segment support
pair and (d) audit identify the exact generic modules and their publication
provenance: trivial-group quotients, supplied-data permutation/reduction,
segment-product data, singleton comparison, inversion counting, filtration
transport and the empty tensor unit. The rank-zero assembly here uses only
that elementary empty-product comparison. None of these generic modules
proves or assumes an excluded full classification conclusion.

The following audit covers every excluded result, all their proofs and
transitive mathematical consequences. The generic uses recorded in its
rows are precisely those inherited from the already audited (d) closure.

| Exclusion, including its proofs and mathematical consequences | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible` | No conclusion or proof dependency. |
| `LinkedSegmentSocleReverseProductStructure` | No conclusion or proof dependency. |
| `LinkedSegmentSoclePairReducible` | No conclusion or proof dependency. |
| `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom` and all their proofs | No conclusion or proof dependency. |
| `SegmentSocleProductIrreducibility` | No conclusion or proof dependency. |
| `AdjacentUnlinkedSegmentSocleSwap` | No conclusion or proof dependency. |
| `TwoSegmentSocleCommutation` | No conclusion or proof dependency. |
| `LinkedSegmentSocleGluing` | No conclusion or proof dependency. |
| `OrderedMultisegmentSocleExistence` | Name occurs only in proposition definitions; no proof is used. |
| Socle exhaustion (`MultisegmentSocleExhaustion`) | Only the explicitly listed generic definitions and tensor/filtration lemmas. |
| Segment analytic classification (`SegmentEssentialSquareIntegrableClassification`) | No conclusion or proof dependency. |
| Special-head multisegment exhaustion (`MultisegmentHeadExhaustion`) | No conclusion or proof dependency. |
| Ordered special-head existence (`OrderedMultisegmentHeadExistence`) | Only the generic data/reduction module in the fixed statement chain. |
| Quotient coverage (`OrderedMultisegmentQuotientExhaustion`) | Only generic trivial-group quotient algebra in the fixed statement chain. |
| Ordered conversion | Only supplied-data permutation transport in the fixed statement chain. |
| Tempered block uniqueness (`TemperedBlockUniqueness`) | No conclusion or proof dependency. |
| `GenericSegmentProductUniqueness` | No conclusion or proof dependency. |
| `SquareIntegrableLanglandsClassification` | Name occurs only in proposition definitions; no proof is used. |
| Square-integrable exhaustion (`SquareIntegrableLanglandsExhaustion`) | No conclusion or proof dependency. |
| Regular exhaustion (`GLRegularLanglandsExhaustion`) | No conclusion or proof dependency. |
| Forward special-segment essential square-integrability | No conclusion or proof dependency. |
| `SegmentHeadProductIrreducibility` and its conclusions | Only the generic constructions just audited; the criterion and its conclusions are absent. |

The strict-monotonicity theorem is deduced from the earlier constituent
result, actual exactness and finite length. It does not use any consumer
irreducibility, commutation, gluing or classification conclusion.

## Development validation

`lean_check` completed the Lake build
with zero errors and zero warnings. Kernel declaration inspection reports
kind `theorem`, universe parameters `uF, uV`, and only `propext`,
`Classical.choice` and `Quot.sound`. These are development checks.
