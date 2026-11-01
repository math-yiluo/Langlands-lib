# Support shift for mirabolic submodules of cuspidal products

Authors: Worker 1070 (Lean statement and Markdown draft), Worker 1166
(verification against the current Library and the source, Markdown update).

This module states one proposition and proves nothing. It records
Bernstein–Zelevinsky's Lemma 4.7(b) in its original mirabolic form: if `W`
is a representation of the mirabolic group `P_n` sitting inside the
restriction of a product of supercuspidal representations
`ρ_1 × ⋯ × ρ_r`, then every irreducible subrepresentation of the highest
derivative of `W` has supercuspidal support which, after the shift by `ν`,
is contained in `{ρ_1, …, ρ_r}` with multiplicities. It is an unproved
assertion.

## The declaration

The module
`Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement`
imports only `Langlands.Representation.Derivative.Homogeneity` and
`Langlands.Representation.Classification.SupercuspidalSupport`. It declares,
in the namespace `Langlands.Classification`,

```lean
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

def CuspidalProductMirabolicSupportShift : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N r : ℕ) (ρ : Fin r → T.CuspidalDatum.{uV, uF}) (h : ∑ i, (ρ i).rank = N + 1)
    (A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) →
    ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear.mirabolic N F.Carrier))
      (f : W ⟶ (Derivative.generalLinearRestriction T N).obj (T.cuspidalProductInduced ρ h A)),
      Function.Injective (SmoothRep.hom f) →
    ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1), Derivative.level T ψ W = k →
    ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier),
      IsIrreducibleSubrepresentation
        ((Derivative.mirabolicDerivativeOfOrder T ψ N k hk).obj W).representation
        σ.representation →
      ∀ s : Multiset (T.CuspidalDatum.{uV, uF}), T.IsSupercuspidalSupport σ s →
        s.map (PadicField.TopologicalData.CuspidalDatum.twist 1) ≤
          (List.ofFn ρ : Multiset (T.CuspidalDatum.{uV, uF}))
```

Its full name is
`Langlands.Classification.CuspidalProductMirabolicSupportShift.{uF,uV} F T`.
The universe parameters are exactly `uF` (the field) and `uV` (the
supercuspidal carriers), in that order, and they are independent. All
representations of `GL_(N+1)`, of the mirabolic group and of `GL_(N+1-k)`
have carriers in `Type (max uF uV)`, the carrier universe of the published
cuspidal product. The prime `p`, the p-adic field `F` and the topology datum
`T` are arbitrary. The proposition installs the supplied topology
`T.topology`; no canonical topology is substituted.

In words: for every nontrivial unitary additive character `ψ` of `F`, every
`N r : ℕ`, every list of cuspidal data `ρ : Fin r → T.CuspidalDatum` with
`∑ i, (ρ i).rank = N + 1` (proof `h`), and every family `A` of actual
supercuspidal representations of `GL_((ρ i).rank)(F)` with each `A i`
representing `ρ i`; for every representation `W` of
`GeneralLinear.mirabolic N F.Carrier` (the source's `P_(N+1)`) and every
intertwiner `f` from `W` to the restriction of the actual product
`A_1 × ⋯ × A_r` to `P_(N+1)` whose underlying linear map is injective; for
every `k` with `0 < k ≤ N + 1` such that `k` is the level of `W`; for every
representation `σ` of `GL_(N+1-k)(F)` that is an irreducible subrepresentation
of the order-`k` derivative of `W`; and for every supercuspidal support `s` of
`σ`: the multiset `s.map (twist 1)`, that is `ν · s`, is a submultiset of
`ρ_1 + ⋯ + ρ_r`.

There are no other premises. In particular `W` is not assumed irreducible,
admissible or of finite length, the ordering of the `ρ_i` is arbitrary, and
no linking or ordering condition is imposed on the cuspidal data.

## The ingredients

All ingredients are published Library declarations; none is redefined here.

- `UnitaryAdditiveCharacter` bundles continuity and nontriviality, so `ψ`
  ranges over the nontrivial continuous unitary additive characters of `F`
  for `T.topology`. BZ77 fixes one such character (§3.1); the proposition
  quantifies over every choice. The same `ψ` defines the level and the
  derivative.
- `T.CuspidalDatum` (`Classification.Segments`) is an element of
  Zelevinsky's set `𝒞`: a rank `r ≥ 1` and an isomorphism class of
  irreducible supercuspidal representations of `GL_r(F)` with carriers in
  `Type uV`. `(ρ i).IsRepresentedBy (A i)` says that the actual
  supercuspidal representation `A i` lies in the class `ρ i`.
- `T.cuspidalProductInduced ρ h A` (`Classification.SupercuspidalSupport`)
  is the source's `ρ_1 × ⋯ × ρ_r`: normalized parabolic induction from the
  standard upper block parabolic of shape `((ρ 1).rank, …, (ρ r).rank)` of the
  external tensor product of the `A i`, a representation of `GL_(N+1)(F)` with
  carrier in `Type (max uF uV)`. By
  `cuspidalProductInducedIsoOfRepresented`, the isomorphism class does not
  depend on the chosen representatives.
- `Derivative.generalLinearRestriction T N`
  (`Derivative.Iteration`) restricts a representation of `GL_(N+1)(F)` along
  the continuous inclusion of `GeneralLinear.mirabolic N F.Carrier`, the
  subgroup of matrices with last row `(0, …, 0, 1)`. This is the source's
  `π|P`. There is no `P_0`; the smallest mirabolic group is `P_1 = {e}`.
- `SmoothRep.hom f` is the underlying linear map of `f`. Injectivity makes
  `W` isomorphic to a `P`-submodule of `π|P`; every `P`-submodule `ω` arises
  this way with `f` the inclusion. The statement is phrased with an injective
  intertwiner so that it applies directly to representations constructed
  elsewhere.
- `Derivative.mirabolicDerivativeOfOrder T ψ N k hk`
  (`Derivative.Homogeneity`) is the actual derivative of order `k` on
  `P_(N+1)`, landing in `GL_(N+1-k)`: an equality transport of the rank
  followed by `k - 1` applications of the published determinant-normalized
  `Φ⁻` and then `Ψ⁻`. This is the source's `τ^(k) = Ψ⁻ (Φ⁻)^(k-1) τ`
  (BZ77 §3.5).
- `Derivative.level T ψ W` (`Derivative.Homogeneity`) is
  `Nat.findGreatest (HasNonzeroDerivative T ψ W) (N + 1)`: the greatest `j`
  with `0 < j ≤ N + 1` whose derivative has a nontrivial carrier, or zero if
  there is none. Hence the premises `0 < k` and `level W = k` say exactly
  that `W^(k) ≠ 0` and `W^(j) = 0` for `k < j ≤ N + 1`: `W^(k)` is the highest
  derivative of `W` in the sense of BZ77 §4.3. They also force `W ≠ 0`.
- `IsIrreducibleSubrepresentation` (`Classification.ConstituentRelations`)
  asks that `σ` be irreducible and that there be an injective intertwiner
  from `σ` into the derivative, so `σ` is an irreducible submodule up to
  isomorphism.
- `T.IsSupercuspidalSupport σ s` (`Classification.SupercuspidalSupport`)
  says that some ordering `ρ'_1, …, ρ'_m` of the multiset `s` has `σ` as an
  irreducible subquotient of `ρ'_1 × ⋯ × ρ'_m`, for actual representatives.
  For `N + 1 - k = 0` this includes `s = 0`, the empty product.
- `CuspidalDatum.twist 1` (`Classification.Segments`) is `ρ ↦ νρ` with
  `ν = |det|` for the residue-normalized absolute value. The comparison
  `≤` on `Multiset` is submultiset inclusion, counting multiplicities.

## Original sources

The proposition is part (b) of the lemma in I. N. Bernstein and
A. V. Zelevinsky, *Induced representations of reductive p-adic groups I*,
Ann. Sci. ENS (4) 10 (1977), 441–472 (literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), file
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Printed page = zero-based PDF index + 440.

- §4.1, printed p. 454 (PDF index 14): for irreducible `ω`, the cuspidal
  `(ρ_1, …, ρ_r)` with `ω ∈ JH(ρ_1 × ⋯ × ρ_r)` are "determined by `ω`
  uniquely up to a permutation"; this unordered collection is `supp ω`. It
  is a multiset, which is how the Library's `IsSupercuspidalSupport`
  records it.
- §4.2, p. 454: `ν(g) = |det g|`.
- §4.3, p. 454: `π^(k) ≠ 0` and `π^(m) = 0` for `m > k` makes `π^(k)` the
  highest derivative.
- §4.7, printed p. 455 (PDF index 15): "LEMMA. — Let `ρ_i ∈ Irr G_(n_i)` be
  cuspidal (`i = 1, …, r`) and `π = ρ_1 × ⋯ × ρ_r`. Then (a) If
  `σ ∈ JH(π^(m))` (`m = 0, 1, …, n`), then `supp σ ⊂ (ρ_1, …, ρ_r)` (see
  4.1). (b) If `ω` is a non-zero `P`-submodule of `π`, `ω^(k)` the highest
  derivative of `ω` and `σ` an irreducible submodule of `ω^(k)`, then
  `ν · supp σ ⊂ (ρ_1, …, ρ_r)`." The proposition of this module is (b) with
  `n = N + 1`.
- §4.8, printed pp. 455–456 (PDF indices 15–16): the proof of (b) passes to
  `π̄ = ν π̃`, which by §2.3(d) and §1.9(f) is the product of the
  `ρ̄_i = ν ρ̃_i`. It restricts the induced pairing of `π` and `π̄` to `P`
  and to `ω`, and applies Proposition 3.8 (printed p. 453, PDF index 13) to
  obtain a pairing of `ω^(k)` with `π̄^(k)` that is non-degenerate with
  respect to `ω^(k)`. Because `σ` is irreducible it deduces
  `σ̃ ∈ JH(π̄^(k))`. The `ρ̄_i` are cuspidal by §2.4(c) and §1.9(f), so (a)
  for `π̄` gives `supp σ̃ ⊂ (ρ̄_1, …, ρ̄_r)`, hence
  `supp σ ⊂ (ν⁻¹ρ_1, …, ν⁻¹ρ_r)`.

**Multiplicities.** The source writes `⊂` between unordered collections. In
the source proof the inclusion comes from (a), which BZ77 deduces from 4.4
and Corollary 4.6: `π^(m)` is glued from the products
`ρ_1^(i_1) × ⋯ × ρ_r^(i_r)` with `i_1 + ⋯ + i_r = m`, and for cuspidal
`ρ_j` of degree `n_j` the derivative `ρ_j^(i)` is `ρ_j` for `i = 0`, the
trivial representation of `G_0` for `i = n_j`, and zero otherwise. So every
irreducible subquotient of `π^(m)` is a subquotient of a product of a
subfamily of the `ρ_j`, and its support is a submultiset of
`(ρ_1, …, ρ_r)`. The submultiset reading is therefore what the source proof
gives, and it is the reading of the Lean conclusion.

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
Ann. Sci. ENS (4) 13 (1980), 165–210 (literature ID
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`), §4.4(d),
printed p. 185, restates (b) for irreducible `ω` of `G_n` as
`νφ_ω − φ_σ ≥ 0`, where `φ` is the multiplicity function of the support and
`(νφ)(ρ) = φ(νρ)`. That restatement is published in the Library as
`Langlands.Classification.HighestDerivativeSupportShift` (module
`Langlands.Representation.Classification.SegmentSocleDerivativesStatement`)
with the same positive twist `CuspidalDatum.twist 1`. The present proposition
is the mirabolic form that the source actually states and proves. Applied to
`W = ω|P` for an irreducible `ω` embedded in some ordering of its cuspidal
product (BZ77 §4.1), it gives the irreducible form, using the uniqueness of
supports. This derivation is documentation; it is not formalized here.

Text extraction of BZ77 pp. 454–456 was used for the quotations above; the
symbols were checked against the structure of the argument. No errata note for
either source was found in the Library `notes/` tree (it has no `errata/`
directory) or in the project literature collection on the date of writing.
This reports that bounded search only.

## Every support of `σ`

The conclusion is asserted for every `s` with `T.IsSupercuspidalSupport σ s`.
In the source `supp σ` is a single multiset because supports are unique
(BZ77 §2.9, §4.1; Zelevinsky 1980, Proposition 1.10). The Library states that
uniqueness separately as
`Langlands.GLSupercuspidalSupportUniquenessStatement`
(`Classification.SupercuspidalSupportStatement`), for positive rank, and
proves it as `Langlands.glSupercuspidalSupportUniqueness`
(`Classification.SupercuspidalSupportUniquenessProof`). This proposition
neither assumes nor imports uniqueness; a proof of the every-support form may
use that theorem, or an argument that applies to each witnessing ordering. If
`σ` had no support, the conclusion would be vacuous; existence of supports is
not asserted here.

## Normalization

The derivative is built from the published determinant-normalized
`Mirabolic.psiMinus` and `Mirabolic.phiMinus`
(`Derivative.MirabolicMinus`), which twist the unnormalized coinvariant
functors by `|det|^(-1/2)` of the output group. The source normalizes by
`mod_U^(-1/2)` (BZ77 §1.8(b), §3.2), and for `m ∈ GL_(n-1)` this module is
`|det m|`. The cuspidal product uses the Library's normalized parabolic
induction. The comparison of these determinant characters with the source's
Haar-modulus normalization is the separate statement task
`a622f240-4846-4086-b34f-f650ba636ee4` with proof task
`f947a735-872d-44db-a9ea-954d17dec4bd`. This proposition concerns the
Library functors as published; it neither assumes nor supplies that
comparison. The direction of the shift agrees with the published
`HighestDerivativeSupportShift`, whose Markdown checks it on segment
representations (Ze80 §3.5: `⟨Δ⟩^(m) = ⟨Δ⁻⟩`, so `ν · supp ⟨Δ⁻⟩ ⊂ supp ⟨Δ⟩`).

## Boundary cases

- **`k = N + 1`.** The derivative lands in `GL_0`, the trivial group, and
  `σ` is a one-dimensional representation of it. Its only support is the
  empty multiset (`r = 0` ordering, empty product), and the conclusion
  `0 ≤ ρ_1 + ⋯ + ρ_r` holds trivially; this case is not proved here.
- **`W = 0`.** Then `level W = 0`, so the premise `level W = k` with `0 < k`
  fails and nothing is asserted. This matches the source's "non-zero
  `P`-submodule".
- **`r = 1`.** Then `π = ρ_1` is supercuspidal, and BZ77 §4.4 forces
  `W^(j) = 0` for `0 < j < N + 1`, so a nonzero `W` has level `N + 1` and the
  previous case applies. This is a consequence of the source, not a premise
  here.
- **`N = 0`.** Then `GL_1`, `P_1 = {e}` and only `k = 1` is allowed.

## Scope and dependencies

The proposition supplies no proof. Statement publication proves no
representation-theoretic assertion. BZ77 Proposition 3.8 (the highest
derivative pairing), Lemma 4.7(a), Corollary 4.6 and the Leibniz
filtration 4.5, the Gelfand–Kazhdan derivatives of supercuspidal
representations (BZ77 §4.4), the contragredient of a product (BZ77 §2.3(d),
§1.9(f)), the uniqueness of supercuspidal supports and the normalization
comparison are inputs of the proof, not hidden hypotheses of this
proposition. None of them is imported here.

This statement is a lower input to the Ze80 §6.2 homogeneity proof task
`b711af72-fdf9-4b32-a450-937911426822` (the case of a submodule of the
restriction that meets the right mixed part trivially), itself a lower input
to ordered-socle existence task `23189526-80b0-4828-a6d4-7ebec2cbeef5`. The
irreducible form `HighestDerivativeSupportShift` (exact proof task
`f81d9b36-2615-4fec-abc2-50ef93d880bf`) is a special case of it. This
module uses no conclusion, proof successor or transitive proof dependency of
any task or proposition excluded by those two tasks. In particular it uses
none of: `SegmentSocleProductIrreducibility` /
`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`; `UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`
and tasks `23e98d90-6055-4e35-91a9-b0f5d8a84961`,
`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc`;
`JuxtaposedSegmentSocleReverseProductStructure`,
`LinkedSegmentSocleReverseProductQuotientHom` and task
`7ff2a1e9-89dc-439e-a861-a567b3db92bf`; `AdjacentUnlinkedSegmentSocleSwap` /
`e3634665-571b-4852-9f4c-bab8a1053434` /
`cded83f3-df9c-4018-bc61-dc54f5c1f9ab`; `TwoSegmentSocleCommutation` /
`426911b4-6620-413f-8065-04b25287f3bd` /
`66e3b87c-647e-41e4-af18-df4d436765f0`; `LinkedSegmentSocleGluing` /
`c84cd52c-3ff3-4024-be50-8b84dd480888` /
`6780b79c-9526-46aa-b8b4-00377d68b1ea`; `OrderedMultisegmentSocleExistence` /
`23189526-80b0-4828-a6d4-7ebec2cbeef5`; socle exhaustion
`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`; analytic segment classification
`aca8805b-054f-4d56-8045-12db7f623404`; special-head exhaustion
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`; ordered special-head existence
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`; quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; ordered conversion
`8252833d-c269-41a9-824c-5879e531b23b`; tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`; `GenericSegmentProductUniqueness` /
`30341ae4-65f2-4a0e-9283-763db01a409e`;
`SquareIntegrableLanglandsClassification` /
`1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`; regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`; forward special-segment essential
square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`;
`SegmentHeadProductIrreducibility` / `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`;
individual segment-socle and special-head existence
`4ca79bbd-589e-476b-9f65-661e799984b5` and
`67279e36-f3c2-42e3-9302-11729784042e`; the segment Jacquet formulas
(`ed48ae06-964c-4c84-9e62-978f5a953ca7`,
`55ad1e10-62d8-46b7-a081-909ef0056426`,
`b95105c6-f8bb-4641-ae53-2f49d1e7f034`,
`92aea10f-62ac-4e0b-bd4a-9a80909797c5`);
`TwoSupercuspidalNonadjacentProductIrreducible` /
`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` and `TwoSupercuspidalProductStructure` /
`ab61f565-1427-4746-ba77-46097563e962`. It uses no segment, cuspidal or
supercuspidal derivative formula (Ze80 §3.5 or §9.6), no proposition of the
Library module `SegmentSocleDerivativesStatement` (the segment-socle part of
task `8e5b4563-0365-41c7-b134-70f2a0b36292`), no segment product
irreducibility criterion (Ze80 4.2 or 9.7), no analytic or
square-integrability result and no classification or exhaustion theorem.
Later proof tasks and lower splits must preserve this exclusion set and the
further exclusions recorded in their contracts.

### Import closure audit

The complete transitive project import closure was traversed in Library
commit `5265467bd3fd94308df2e30a20d91abedd90f413`, the base of this
contribution. It has the 79 project modules listed below. Every one has a
nonempty Markdown pair, and every pair is byte-identical between that
Library tree and the submitting workspace. The derivative branch contains
group and functor constructions, quotient carriers, rank transports, the
finite-maximum level and the invariant-subspace homogeneity definition, with
elementary laws about them. The classification branch contains the cuspidal
data and their real-power twists, supercuspidal representations and classes,
the constituent relations, normalized parabolic induction, cuspidal products
and the support definitions. The closure contains no socle, segment-product,
classification, commutation, exhaustion, coverage, derivative-filtration,
derivative-detection, derivative-exactness, pairing or Whittaker-finiteness
result, no `Statement` module of any derivative or classification
proposition, and no module of any excluded task above. The `Proof` modules in
the closure prove p-adic arithmetic normalization interfaces,
matrix-coefficient laws, smooth-part laws, smoothness and admissibility
transfer, the admissibility equivalence, character-twist laws and the
isomorphism invariance of irreducibility; none concerns derivatives,
supports or classification. The one other theorem-bearing module,
`Langlands.Topology.CompactNormCharacter` (imported by
`Group.GL.NormalizedCharacter`), proves only that a continuous homomorphism
to `ℝ≥0ˣ` is trivial on a compact subgroup.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
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
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
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
Langlands.Representation.Unitary.Basic
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.Operations
```

### Development checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(diagnostic `1a783d43-4071-4554-91f8-557222e9e52a`) compiled the module with no errors or warnings.
Inspection of the declaration reported `statement_returns_prop: true`, level
parameters `uF, uV`, and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. These checks establish elaboration and
proposition kind only; they are not semantic acceptance.
