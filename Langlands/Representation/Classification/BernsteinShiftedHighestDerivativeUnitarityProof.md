# Irreducibility and unitarizability of the shifted highest derivative

Author: Worker 4876. This module proves the published proposition
`Langlands.Classification.BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T`
(module `BernsteinUnitaryStatement`; Bernstein 1984 §7.4, Tadić 1986 Theorem
2.5(iii)). For every `N > 0`, every unitary additive character `ψ`, every
irreducible unitarizable actual smooth representation `π` of `GL_N` with
carrier in `Type (max uF uV)` and every highest-derivative order datum `hd` of
`π`, the shifted highest derivative `ν^(1/2) π^(h)`
(`shiftedHighestDerivative F T ψ hd`) is irreducible and unitarizable.

The final theorem is

```lean
theorem Langlands.Classification.bernsteinShiftedHighestDerivativeUnitarity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T
```

It has no hypotheses beyond the statement's own. It applies
`bernsteinShiftedHighestDerivativeUnitarity_of_unitarizability` (below) to the
published proof `bernsteinShiftedHighestDerivativeUnitarizability` of the
unitarizability half `BernsteinShiftedHighestDerivativeUnitarizability`
(module `BernsteinShiftedHighestDerivativeUnitarizabilityProof`).

The conditional theorem
`bernsteinShiftedHighestDerivativeUnitarity_of_unitarizability F T hunit`
derives `BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T` from
`hunit : BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T`. The
unitarizability half thus implies the whole statement: unitarizability of
`ν^(1/2) π^(h)` already forces irreducibility of `π^(h)`. The proof does not use
Zelevinsky's Theorem 8.1 or `GeneralLinearHighestDerivativeIrreducibility`. It
uses only proved Library results. There are no axioms beyond the standard ones,
no proof holes and no option changes besides the
`backward.isDefEq.respectTransparency.types false` setting copied from
`Aubert/ZelevinskyHighestDerivative`.

## Idea

Let `π` be irreducible on `GL_N`, `N > 0`. Zelevinsky's exhaustion realizes `π`
as an irreducible subrepresentation of a precedence-ordered product
`⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` of segment socles. With `λ = Σ rank Δ_i`, homogeneity
of that product forces the highest derivative order of `π` to be `λ`. The
order-`λ` derivative of the product is a precedence-ordered product
`⟨Δ_1⁻⟩ × ⋯`, and that product has a unique irreducible subrepresentation. So
`π^(λ)` embeds in a representation with a unique irreducible
subrepresentation. If `ν^(1/2) π^(λ)` is unitarizable, `π^(λ)` is semisimple,
because it is admissible of finite length. A semisimple nonzero
representation with at most one irreducible subrepresentation is irreducible.

## Declarations (namespace `Langlands.Classification.ShiftedHighestDerivative`, except the last)

- `isIrreducible_of_complemented_of_isIrreducibleSocle`. Take a group `G`, a
  nontrivial finite-length smooth `A`, and an injective map `ι : A ⟶ Y`.
  Suppose the subrepresentation lattice of `A` is complemented and
  `IsIrreducibleSocle Y.representation π₀`, meaning every irreducible
  injective intertwiner into `Y` has the same range. Then `A` is irreducible.
  Finite length makes the lattice atomic, through the Library's order
  isomorphism with group-algebra submodules. For two atoms `U₁` and `U₂`,
  the irreducible restrictions
  (`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`)
  composed with `ι` have equal ranges. Since `ι` is injective, this gives
  `U₁ ≤ U₂`. For any `S` with complement `C`, if both were nonzero they would
  contain atoms `U₁ ≤ S` and `U₂ ≤ C`. Then `U₁ ≤ S ⊓ C = ⊥`, a contradiction.
  So every `S` is `⊥` or `⊤`, and `⊥ ≠ ⊤` because `A` is nontrivial.

- `complementedLattice_of_isUnitarizable_segmentFactor`. Let `A` be a
  finite-length smooth representation of `GL_r` such that
  `T.segmentFactor A (1/2)` is unitarizable. Then
  `Subrepresentation A.representation` is complemented. Irreducible smooth
  representations of `GL_r` are admissible (`CuspidalSupport.cuspidalEmbedding`),
  so finite-length ones are admissible too
  (`SmoothRep.isAdmissible_of_finiteLength_of_irreducible`). Admissibility
  passes to the twist (`isAdmissible_twist_iff`). Compact open subgroups are
  cofinal (`T.generalLinearCompactOpen`). Then
  `admissibleUnitarySemisimplicity` makes the twist semisimple, and the
  twist's lattice is order-isomorphic to that of `A`
  (`twistSubrepresentationOrderIso`).

- `isIrreducible_highestDerivative F T hN ψ π hπ hd hu`. For irreducible `π` on
  `GL_N`, `N > 0`, highest-order data `hd`, and `hu` stating that
  `T.segmentFactor (π^(hd.order)) (1/2)` is unitarizable, `π^(hd.order)` is
  irreducible. The proof runs as follows.
  1. `multisegmentSocleExhaustion` gives a precedence-ordered segment-socle
     datum `d` and an injective intertwiner `j : π → d.induced`.
  2. The first part copies the Library proof of
     `Aubert.ZelevinskyHighestDerivative.exists_label_subquotient`.
     `segmentSocleProductHighestDerivative` gives the vanishing of the
     derivatives of `d.induced` above `λ`, and an isomorphism `e` of the
     order-`λ` derivative with `d'.induced`, where `d'` has segment socles and
     segments `Δ_i⁻`. `precedenceOrdered_endpointSeparated` and
     `segmentSocleProductHomogeneity` make the restricted product homogeneous of
     level `λ` (`level_eq_iff`, `segmentSocleProduct_nontrivial`).
     `LevelCalculus.level_eq_of_isHomogeneous` transports the level to `π`, so
     `π^(λ)` is nontrivial.
  3. `hd.order = λ`. A smaller order contradicts `hd.higher_vanish` at `λ`. A
     larger order contradicts `hd.nonzero`: the derivative of `j` at that order
     is injective (`generalLinearDerivativeExactness`) into a zero
     representation.
  4. After rewriting the order to `λ`, the derivative of `j` followed by `e`
     embeds `π^(λ)` into `d'.induced`. That product has finite length
     (`SegmentProductClass.hasFiniteLength_induced`), so `π^(λ)` does too. `d'`
     is precedence-ordered (`segmentInitialTruncationOrder`), so
     `orderedMultisegmentSocleExistence` gives `π₀` with
     `IsIrreducibleSocle d'.induced.representation π₀.representation`. The two
     lemmas above conclude.

- `bernsteinShiftedHighestDerivativeUnitarity_of_unitarizability`: for `N`,
  `ψ`, `π` and `hd` as in the target, `hunit` gives unitarizability of
  `shiftedHighestDerivative F T ψ hd`. `isIrreducible_highestDerivative` gives
  irreducibility of `π^(h)`, and `isIrreducible_twist_iff` moves it to the
  twist.

## Final theorem (namespace `Langlands.Classification`)

`bernsteinShiftedHighestDerivativeUnitarity F T` is
`bernsteinShiftedHighestDerivativeUnitarity_of_unitarizability F T` applied to
`bernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T`.

## Sources

The overall assertion is Bernstein 1984, §7.4 and its Remark (printed p.83), and
Tadić 1986, Theorem 2.5(iii). The ingredients are Zelevinsky 1980, Theorems
6.1, 6.2 and the product part of 6.6, through their Library proofs. The
argument through semisimplicity of unitarizable admissible representations
replaces Zelevinsky's Theorem 8.1. It applies only to unitarizable shifted
derivatives, which is the case of the target.
