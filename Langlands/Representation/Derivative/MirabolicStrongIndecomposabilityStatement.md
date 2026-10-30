# Highest-derivative strong indecomposability reduction

Authors: Worker 700 (Lean statement and initial Markdown, shared draft
revision 2 of task `ff4738d8-47e3-433b-bedc-629bc2d492a7`) and Worker 749
(source check, Markdown revision and import audit).

This module states one proposition and proves nothing. It records Zelevinsky's
criterion for strong indecomposability of a representation of a mirabolic
group in terms of homogeneity and its highest derivative. It also records the
positivity of the derivative level of a nonzero representation, which that
criterion presupposes. Both are unproved assertions of the proposition.

## The declaration

The module `Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityStatement`
imports only `Langlands.Representation.Derivative.Homogeneity` and
`Langlands.Representation.Classification.StrongIndecomposability`. It declares,
in the namespace `Langlands.Derivative`,

```lean
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

def MirabolicStrongIndecomposabilityReduction : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic N F.Carrier)),
    (Nontrivial A → 0 < level T ψ A) ∧
      ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
        Nontrivial A → k = level T ψ A →
          (Classification.IsStronglyIndecomposable A.representation ↔
            IsHomogeneous T ψ A ∧
              Classification.IsStronglyIndecomposable
                ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).representation)
```

Its full name is `Langlands.Derivative.MirabolicStrongIndecomposabilityReduction.{uF,uV} F T`.
The universe parameters are exactly `uF` (the field) and `uV` (the carriers),
in that order, and they are independent. The prime `p`, the p-adic field `F`
and the topology datum `T` are arbitrary. The proposition installs the
supplied topology `T.topology`; no canonical topology is substituted.

For every unitary additive character `ψ` of `F`, every `N : ℕ` and every
smooth complex representation `A` of `GeneralLinear.mirabolic N F.Carrier`
with carrier in `Type uV`, it asserts two clauses:

1. **Positive level.** If the carrier of `A` is nontrivial, then
   `0 < level T ψ A`.
2. **Highest-derivative criterion.** For every `k : ℕ` and every proof
   `hk : 0 < k ∧ k ≤ N + 1`: if the carrier of `A` is nontrivial and
   `k = level T ψ A`, then `A` is strongly indecomposable if and only if `A`
   is homogeneous and the order-`k` derivative
   `(mirabolicDerivativeOfOrder T ψ N k hk).obj A` is strongly
   indecomposable.

There are no other premises. No finite length, Artinian, irreducibility,
admissibility, plus-model, exactness, derivative-detection, filtration or
classification hypothesis appears in either clause.

## The ingredients

All ingredients are published Library declarations; none is redefined here.

- `UnitaryAdditiveCharacter` bundles continuity and nontriviality, so `ψ`
  ranges over the nontrivial continuous unitary additive characters of `F`
  for the topology `T.topology`. Bernstein–Zelevinsky fix one arbitrary
  nontrivial additive character in §3.1; the proposition quantifies over
  every such choice.
- `GeneralLinear.mirabolic N F.Carrier` is the subgroup of
  `GL_(N+1)(F)` of matrices with last row `(0, …, 0, 1)`. It is the source's
  `P_n` for `n = N + 1`. `Nontrivial A` refers to the carrier of `A`.
- `Classification.IsStronglyIndecomposable ρ` is the intrinsic intersection
  condition `∀ S T : Subrepresentation ρ, S ≠ ⊥ → T ≠ ⊥ → S ⊓ T ≠ ⊥` on
  Mathlib's actual lattice of invariant subspaces. It involves no chosen
  socle, embedding or irreducible factor. It holds vacuously for a zero
  carrier.
- `mirabolicDerivativeOfOrder T ψ N k hk` is the order-`k` derivative
  functor from representations of `P_(N+1)` to representations of
  `GL_(N+1-k)`. It is the equality transport of the source rank
  `N = (N+1-k) + (k-1)` followed by `mirabolicDerivative T ψ (N+1-k) (k-1)`,
  that is, `k - 1` applications of the published `Φ⁻` followed by `Ψ⁻`. This
  is the source's `τ^(k) = Ψ⁻ (Φ⁻)^(k-1) (τ)`. Order one is exactly
  `Mirabolic.psiMinus T N` (`mirabolicDerivativeOfOrder_one`). The functor
  does not depend on the proof `hk` (`mirabolicDerivativeOfOrder_proof_irrel`),
  and its carriers stay in `uV`. No order-zero mirabolic derivative is
  introduced.
- `level T ψ A` is `Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1)`:
  the greatest order `k` with `0 < k ≤ N + 1` whose derivative has a
  nontrivial carrier, or zero if there is no such order. Zero is a
  totalization default, not a derivative order.
- `IsHomogeneous T ψ A` says that every nonbottom invariant subspace `U` of
  `A` satisfies `level T ψ (SmoothRep.subrepresentation A U) = level T ψ A`,
  where `SmoothRep.subrepresentation A U` is `U` with its restricted smooth
  action.

## Original sources

The proposition follows A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*, Ann.
Sci. ENS (4) 13 (1980), 165–210 (literature ID `zelevinsky-1980-induced-ii`,
SHA256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`).

- §4.3, printed p. 184 / one-based PDF page 21: for `π ∈ Alg P_n`, "the
  maximal number `k` such that `π^(k) ≠ 0` is called the level … of `π`",
  and `π^(k)` is then the highest derivative.
- §5.1, printed p. 187 / PDF page 24: `τ ∈ Alg P` is homogeneous if
  `λ(σ) = λ(τ)` for each nonzero submodule `σ ⊂ τ`. The Proposition there
  shows, for `λ(τ) = k`, that homogeneity is equivalent to every nonzero
  submodule meeting the submodule `(Φ⁺)^(k-1) Ψ⁺ (τ^(k))` of `τ`
  nontrivially.
- §5.4, printed p. 188 / PDF page 25, Proposition: "Let `τ ∈ Alg P_n` and
  `k = λ(τ)` be the level of `τ`. The following are equivalent: (1) `τ` is
  strongly indecomposable. (2) `τ` is homogeneous and `τ^(k)` is strongly
  indecomposable." Clause 2 is this Proposition.

The lower source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472 (literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`).

- §3.2, printed p. 451 / PDF page 12: the functors `Ψ⁻`, `Ψ⁺`, `Φ⁻`, `Φ⁺`
  are exact, with the adjunctions and the exact sequence
  `0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0`.
- §3.3(a), same page: `Φ⁺` and `Ψ⁺` induce isomorphisms of submodule lattices.
- §3.5, printed p. 452 / PDF page 13: the derivatives `τ^(k)`,
  `k = 1, …, n`, and the natural filtration
  `0 ⊂ τ_n ⊂ … ⊂ τ_1 = τ` with
  `τ_k / τ_(k+1) ≅ (Φ⁺)^(k-1) Ψ⁺ (τ^(k))`.

**Clause 1 is a consequence of the §3.5 filtration.** If every derivative
`τ^(k)` with `1 ≤ k ≤ n` vanishes, every layer of the filtration vanishes and
so `τ = 0`. Hence a nonzero `τ` has a nonzero derivative of some positive
order, and its level is positive. Zelevinsky uses this tacitly when he speaks
of the level and the highest derivative of an arbitrary representation of
`P_n`. In the Library, positivity is not a consequence of the finite-maximum
definition of `level`: `level_pos_iff` only says that positive level is
equivalent to some nonzero derivative. So clause 1 is a substantive analytic
detection assertion, and it is not proved here.

**Clause 2 is Ze80 §5.4.** Zelevinsky's proof considers the submodule
`τ_k = (Φ⁺)^(k-1) Ψ⁺ (τ^(k)) ⊂ τ` for `k = λ(τ)`, the essential highest
layer of the filtration. By BZ77 §3.3(a) the submodule lattices of `τ_k` and
`τ^(k)` are isomorphic, so `τ_k` is strongly indecomposable exactly when
`τ^(k)` is. With §5.1 (1)⇔(2), condition (2) becomes "`τ_k` is strongly
indecomposable and meets every nonzero submodule of `τ`", which is trivially
equivalent to strong indecomposability of `τ`. This module asserts neither
the highest-layer embedding nor the lattice isomorphism; both are obligations
of later proof tasks.

**Errata.** No errata note for either source exists in the project
literature collection or in the Library's notes. The published note
`notes/henniart/segment-head-independence.md`, which also relies on BZ77
§3.5, likewise located no matching errata entry. No known correction affects
the passages used here.

## Normalization

The imported `Φ⁻` and `Ψ⁻` are the published determinant-normalized minus
functors, which twist by the absolute value of the determinant to the power
`-1/2` at each step in place of the source's `mod_U^(-1/2)` (BZ77 §1.8). The
comparison of those determinant characters with the source's Haar-modulus
normalization is a separate, still pending proof obligation; this
proposition neither assumes nor supplies it. The published twists act on
the same carriers (`Langlands.Representation.Category.Twist`), so the
normalization does not change which derivative carriers are nonzero; this
remark explains the convention and is not proved in this module.

## Boundary cases

- **Zero representations.** A representation on a zero carrier is strongly
  indecomposable and homogeneous vacuously and has level zero
  (`level_eq_zero_of_subsingleton`). It has no positive highest order, so it
  is excluded from both clauses by the explicit `Nontrivial A` premise. In
  the source, §5.4 with `τ = 0` has no level in `1, …, n`.
- **Positive-order indexing.** Clause 2 quantifies over `k` with
  `0 < k ≤ N + 1` and the equation `k = level T ψ A`. If `A` is nontrivial,
  clause 1 and `level_le` show that `k = level T ψ A` satisfies this bound,
  so clause 2 applies to the actual highest order. For any other `k` the
  clause is vacuous.
- **Order one.** When the level is one, the derivative is `Ψ⁻(A)` itself.
- **Top order and `N = 0`.** Order `N + 1` has target `GL_0`. For `N = 0`,
  i.e. `P_1`, the only valid order is one, the functor `P_1 → GL_0`. Since
  `GL_0` is a trivial group, strong indecomposability of a `GL_0`
  representation means that every two nonzero subspaces of its carrier meet,
  that is, the carrier has dimension at most one. This elementary reading is
  not formalized here.

## Scope and dependencies

The proposition supplies no proof of either clause. Definition and statement
publication proves no analytic assertion. The source proof inputs named
above (the §3.5 filtration, exactness, the §3.3(a) lattice isomorphisms, the
essential highest layer and §5.1) and the normalization comparison are
obligations of later proof tasks, not hidden hypotheses of this proposition.

This statement is a lower input to the independent ordered-socle existence
task `23189526-80b0-4828-a6d4-7ebec2cbeef5`. It uses no conclusion, proof
successor or transitive proof dependency of that task, of socle exhaustion
`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, of analytic segment classification
`aca8805b-054f-4d56-8045-12db7f623404`, of segment-socle product
irreducibility `23e98d90-6055-4e35-91a9-b0f5d8a84961`, of the final
segment-socle irreducibility criterion
`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`, of `AdjacentUnlinkedSegmentSocleSwap`
or `TwoSegmentSocleCommutation`, of the special-head product criterion
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, special-head exhaustion
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered special-head existence
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`,
`SquareIntegrableLanglandsClassification` /
`1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`, `GenericSegmentProductUniqueness` /
`30341ae4-65f2-4a0e-9283-763db01a409e`, ordered special-segment conversion
`8252833d-c269-41a9-824c-5879e531b23b`, or forward special-segment essential
square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`. Later proof
tasks and lower splits must preserve this exclusion set.

### Import closure audit

The complete transitive project import closure was traversed in Library
commit `3987c3d7445531c2c7f784464a3fd47061ba0865`, the base of this
contribution. It has the 55 project modules listed below. Every one has a
nonempty Markdown pair, and every pair is byte-identical between that
Library tree and the submitting workspace. The derivative branch contains
group and functor constructions, quotient carriers, rank transports, the
finite-maximum level and the invariant-subspace homogeneity definition, with
elementary laws about them. The strong-indecomposability branch adds the
subrepresentation lattice and the intersection predicate. The closure
contains no socle, segment, classification, commutation, exhaustion,
coverage, derivative-filtration or derivative-detection result, and no module
of any excluded task above. The `Proof` modules in the closure prove the
p-adic arithmetic normalization interfaces, the matrix-coefficient laws,
smoothness and admissibility transfer, and character-twist laws; none
concerns derivatives, socles or classification.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.StrongIndecomposability
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.SubrepresentationLattice
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.Nonarchimedean.Subgroup
```

### Development checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled
the module with no errors or warnings. Inspection of the declaration reported
`statement_returns_prop: true`, level parameters `uF, uV`, and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. A private
scratch check, not part of this module, confirmed by `Iff.rfl` that the
proposition unfolds to the literal two-clause statement with the intersection
predicate, the homogeneity condition and the rank-transport-then-iteration
derivative spelled out. It also confirmed that at order one clause 2
specializes to `Ψ⁻` by `mirabolicDerivativeOfOrder_one`. These checks
establish elaboration and proposition kind only; they are not semantic
acceptance.
