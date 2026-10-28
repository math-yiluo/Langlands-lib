# Constituent commutativity of a product of two irreducible GL factors

Author: Worker 763. Worker 238 supplied the exact target shape and compiled
it first as a private probe.

`Langlands.Classification.TwoFactorProductConstituentCommutativity.{uF,uV} F T`
is a Prop-valued definition. It states that the two orders of a normalized
product of two irreducible factors have the same composition factors. This
module supplies no proof of that assertion.

## Exact statement

Fix any prime `p` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and the
supplied `T : F.TopologicalData`. The definition installs `T.topology`. For
every `n : ℕ`, every `B : GeneralLinear.BlockShape n` with
`h₂ : B.length = 2`, and every family

```text
A : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)
```

with `∀ i, (A i).IsIrreducible`, put `σ := B.adjacentSwap 0 _`, where the
omitted proof of `0 + 1 < B.length` comes from `h₂`. The conclusion is

```text
HaveSameJordanHolderFactors
  (Rep.of ((T.normalizedProductInductionFunctor B).obj A).representation)
  (Rep.of ((T.normalizedProductInductionFunctor (B.permute σ)).obj
    (fun i => A (σ i))).representation)
```

## Scope and conventions

- `B.adjacentSwap 0 _` is the transposition `Equiv.swap 0 1` of the two
  block labels. `BlockShape.permute` makes new block `i` equal to old block
  `σ i`, definitionally of size `B.size (σ i)`. This is the convention of
  `SegmentProductDatum.permute` and `Classification.AdjacentUnlinkedSegmentSwap`.
  Writing `π₁ = A 0` and `π₂ = A 1`, the left side is the normalized product
  `π₁ × π₂` on `GL_n(F)` and the right side is `π₂ × π₁`.
- Both products are the actual objects of the published
  `T.normalizedProductInductionFunctor`: the standard upper block parabolic,
  the positive half-modulus normalization and right translation, with the
  tensor product of the factors as inducing representation.
- `HaveSameJordanHolderFactors` (in `Representation.Filtration.ObjectDefinitions`)
  asks for actual finite composition series of the same length of both
  representations, with simple graded quotients, and a permutation matching
  each quotient to an isomorphic quotient. The conclusion therefore includes
  that both products have finite length. It is sensitive to multiplicities. It is not an
  isomorphism of the two products, an identity in a Grothendieck group, or an
  equality of abstract parameters.
- The only representation-theoretic hypothesis is irreducibility of the two
  factors. There is no cuspidality, segment, genericity, unitarity,
  admissibility, finite-length or order hypothesis. The two factors may be
  equal or isomorphic, and their ranks may be equal.
- The field universe `uF` and the factor carrier universe `uV` are
  independent. The prime, the p-adic field and the compatible topology are
  arbitrary.
- All ranks `n` are quantified. A shape of length two has two positive block
  sizes summing to `n`, so `n ≥ 2`. Rank zero and rank one are vacuous.

## Source correspondence

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
pp.165–210. Source `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
PDF page numbers are one-based.

- Theorem 1.9, printed p.174 (PDF p.11): the ring `R` is commutative, that
  is, if `π₁ ∈ Alg G_k` and `π₂ ∈ Alg G_l` have finite length, then
  `π₁ × π₂` and `π₂ × π₁` have the same composition factors,
  `JH⁰(π₁ × π₂) = JH⁰(π₂ × π₁)`.
- Remark 1.8 on the same page and §1.7, printed pp.172–173 (PDF pp.9–10),
  define the product `ρ₁ × … × ρ_r = i_{(n),(n₁,…,n_r)}(ρ₁ ⊗ … ⊗ ρ_r)` with
  Zelevinsky's normalized induction functor of §1.1, printed p.170 (PDF p.7).
  `JH⁰` is the multiset of composition factors, so equality is counted with
  multiplicities. Proposition 1.4 on printed p.171 (PDF p.8) shows that these
  products of finite-length factors have finite length.

This definition is the special case in which both factors are irreducible.
An irreducible representation has length one, so the special case is
contained in Theorem 1.9. The finite length of both products, which
Zelevinsky takes from Proposition 1.4, is part of this conclusion and not a
hypothesis. Zelevinsky's product order matches `BlockShape`: the first factor
occupies the first block. The irreducible case suffices for the known
consumers. It is also the base case from which the finite-length form,
owned separately by task `bd34fb90-1c0d-4f74-aed4-ef6af4d9e5af`, is to be
derived. That task depends on this one; this statement and its proof use no
finite-length form of Theorem 1.9.

The cited passages were read in the retained original, and its hash was
checked.

## Source proof and planned route

Zelevinsky's proof uses `s_n` with `(s_n)_{ij} = (-1)^i δ_{i,n+1-j}` and the
automorphism `s(g) = s_n (gᵗ)⁻¹ s_n⁻¹` of `GL_n`. The induced functor `s` on
smooth representations satisfies two parts of a lemma.

- (a) `s(π₁ × π₂) ≅ s(π₂) × s(π₁)` for all `π₁, π₂`. Zelevinsky says this
  follows from the definitions.
- (b) If `π` has finite length, then so does `s(π)`, and
  `JH⁰(s(π)) = JH⁰(π̃)`, where `π̃` is the smooth contragredient. This reduces
  to irreducible `π`, where it is the Gelfand–Kazhdan theorem. Zelevinsky
  cites his reference [8], Gelfand–Kazhdan (1974), and his reference [2],
  Bernstein–Zelevinsky (1976), 7.3.

The proof then computes

```text
JH⁰(π₁ × π₂) = JH⁰((s(π₁ × π₂))~) = JH⁰((s(π₂) × s(π₁))~)
             = JH⁰((s(π₂))~ × (s(π₁))~) = JH⁰(π₂ × π₁),
```

using in turn (b), (a), §1.1(d) (normalized induction commutes with
contragredients), and (b) again.

The planned independent proof follows this route.

1. Lemma (a). The published `Parabolic.NormalizedProductInverseTransposeClause`
   (`Representation/Parabolic/InverseTransposeProductStatement`, proved in
   `InverseTransposeProductProof` by task
   `fc1a5e69-5e8e-4fcd-ad69-c3d3d1384e91`) identifies the inverse-transpose
   pullback of a normalized product over `B` with the product over
   `B.reverse` of the pulled-back factors. It uses the plain inverse
   transpose `θ(g) = (gᵗ)⁻¹` and already reverses the block order.
   Zelevinsky's extra conjugation by `s_n` is inner, so it does not change
   isomorphism classes. For a shape of length two, `B.reverse` and
   `B.permute σ` have the same sizes but are different terms, and the proof
   must compare them explicitly. The clause covers positive ranks, which
   includes every rank here.
2. Lemma (b) for the irreducible factors and for the composition factors of
   both products. The Gelfand–Kazhdan theorem is
   `GelfandKazhdanContragredientStatement` (proof task
   `2206daa6-e219-4ed6-9ad1-4f4d47efed93`, pending). It assumes admissibility,
   is phrased with `Matrix.GeneralLinearGroup (Fin (n + 1))`, and uses the
   canonical normed-field topology. Irreducible smooth representations must
   therefore be shown to be admissible. Zelevinsky §1.5, printed p.171
   (PDF p.8), takes this from his reference [1], Bernstein–Zelevinsky (1977),
   2.5. The Library states the product-Levi form as
   `CuspidalSupport.IrreducibleLeviAdmissibilityTheorem`, but no proof of it
   was found at this writing. The topology and rank conventions must also be
   reconciled with `T.topology`.
3. Finite length of the products is the statement
   `Classification.IrreducibleProductFiniteLength` (proof task
   `0717fd42-d711-4f42-8269-f6ae4c8da1e9`, pending). Converting finite module
   length to an actual composition series in `ObjectRepFiltration` form is a
   separate step.
4. Transport of composition series along pullback by a group automorphism
   and along the smooth contragredient of a finite-length admissible
   representation. Exactness of the smooth contragredient and admissible
   reflexivity are published with proofs in `Smooth/Contragredient`
   (`ExactProof`, `AdmissibleDualityProof`). The published
   `Parabolic.naturalNormalizedInductionDuality` proves that smooth duality
   commutes with normalized induction. Together with a comparison of the
   contragredient of a two-factor tensor product, this is the input for
   §1.1(d) on a two-block product. The published Jordan–Hölder tools in
   `Filtration/JordanHolderComparisonProof` and `Filtration/LengthTwoMatching`
   handle comparison, transport and transitivity of
   `HaveSameJordanHolderFactors`.

Zelevinsky's Remark 1.12(a) on printed p.175 (PDF p.12) notes that the
theorem can also be proved by computing characters. Such a route is
acceptable instead if its inputs become available. The published
`CuspidalSupport.AdjacentBlockSwapCuspidalInductionFactorsTheorem` covers
only irreducible cuspidal inducing data. That is the case Remark 1.12(a)
attributes to Bernstein–Zelevinsky (1977), 2.9. It may help a proof, but it
does not give this result for arbitrary irreducible factors such as segment
socles.

The proof successor must check the exact hypotheses, universes and
transitive dependencies of each input. It should reuse or wait for existing
owners and split off only inputs that have no owner. A proposition
definition, citation, conditional assembly or pending task is not a proved
input.

## Independence

This result is a lower input of linked two-factor gluing
(`LinkedSegmentSocleGluing`, candidate `c84cd52c-3ff3-4024-be50-8b84dd480888`,
and its proof successor), two-segment socle commutation
`426911b4-6620-413f-8065-04b25287f3bd`, the adjacent unlinked segment-socle
swap `e3634665-571b-4852-9f4c-bab8a1053434`, linked full-product reduction
`0f459af5-e039-4eee-a8bd-9d8d2f508936` and independent socle exhaustion
`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`. Its proof must not use any of them.
It must also avoid the segment-socle irreducibility criterion
`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`, Worker 250's two-segment statement
task `16045335-62c9-4da7-b38f-88579104274b`, the finite-length form
`bd34fb90-1c0d-4f74-aed4-ef6af4d9e5af`, ordered socle existence
`23189526-80b0-4828-a6d4-7ebec2cbeef5`, segment analytic classification
`aca8805b-054f-4d56-8045-12db7f623404`, multisegment special-head exhaustion
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered special-head existence
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`, the square-integrable Langlands
classification `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable
exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4` and regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`. These exclusions cover their
conclusions, proof successors and transitive proof dependencies.
