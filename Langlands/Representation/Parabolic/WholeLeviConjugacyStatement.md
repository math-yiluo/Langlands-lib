# Weyl conjugacy invariance of finite-length normalized induction

Author: Worker 757.

This pair defines one proposition,
`Langlands.Parabolic.WholeLeviInductionConjugacy.{uF, uV, uW}`. It is a derived,
`GL_n`-specific, finite-length form of the Weyl conjugacy invariance of
normalized parabolic induction: conjugate inducing data on conjugate standard
Levi subgroups induce to representations with the same composition factors,
counted with multiplicity. The declaration is a `Prop`-valued `def`. This
contribution does not prove it. Its proof is a separate task, and no
Grothendieck-group (`K0`) comparison theorem is supplied here.

## Exact statement

The outer parameters are a prime natural number `p` with `[Fact p.Prime]`, an
actual `p`-adic field `F : PadicField.{uF} p` (a finite extension of `ℚ_p`), and
a compatible topological realization `T : F.TopologicalData`. The body first
installs the supplied topology `T.topology` on `F.Carrier`. Then, for all

- `n : ℕ` and block shapes `B C : GeneralLinear.BlockShape n`,
- `w : Equiv.Perm (Fin n)` and
  `hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) B C w`,
- `σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)` and
- `τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)`,

the hypotheses are exactly

1. `σ.HasFiniteLength`,
2. `τ.HasFiniteLength`, and
3. `Nonempty ((CuspidalSupport.transport B C w hw σ.representation).Equiv τ.representation)`.

With `T.generalLinearTopologicalGroup n` installed, the conclusion is

```
HaveSameJordanHolderFactors
  (Rep.of (T.normalizedParabolicInduced B σ.representation))
  (Rep.of (T.normalizedParabolicInduced C τ.representation))
```

Both inductions are representations of the same group `GL_n(F)`.

## Definitions and conventions

All definitions are the published ones, used unchanged.

- `BlockShape n` (`Langlands.Group.GL.Blocks`) is an ordered list of positive
  block sizes with sum `n`. `B.Levi F.Carrier` is the product
  `∏_i GL_(B.size i)(F)` of the actual block groups, and `B.leviSubgroup` is
  its image in `GL_n(F)`, the block-diagonal matrices.
- `permutation n F w` (`Langlands.Group.GL.Maps`) is the permutation matrix
  sending the standard basis vector `e_j` to `e_(w j)`; its `(i, j)` entry is
  `1` exactly when `w j = i`.
- `ConjugatesLevi B C w`
  (`Langlands.Representation.CuspidalSupport.LeviDefinitions`) says that the
  image of the whole subgroup `B.leviSubgroup` under conjugation
  `g ↦ P_w g P_w⁻¹` by `P_w = permutation n F w` equals `C.leviSubgroup`. It
  identifies the whole embedded Levis, not only their block sizes.
  `leviConjugation B C w hw : B.Levi ≃* C.Levi` is that matrix conjugation,
  read through the two block-diagonal embeddings.
- `transport B C w hw ρ` is `ρ ∘ (leviConjugation B C w hw)⁻¹`, so
  `(transport ρ)(m') = ρ(P_w⁻¹ m' P_w)` for `m'` in the `C`-Levi (the
  published `leviConjugation_symm_embedding`). This is inverse conjugation;
  the docstring of `transport` cites BZ77 §1.7 for this convention. The
  transported representation keeps the carrier of `σ`, so hypothesis 3 is an actual `Representation.Equiv` between
  carriers in the independent universes `uV` and `uW`.
- `SmoothRep.HasFiniteLength` (`Langlands.Representation.Category.Basic`) is
  finite length of the carrier as a module over the group algebra `ℂ[G]` of
  the whole Levi. It is not finite dimension over `ℂ`, and it is not a
  condition on separate tensor factors.
- `T.normalizedParabolicInduced B ρ`
  (`Langlands.Representation.Induction.Parabolic`) is normalized parabolic
  induction from the standard upper block-triangular parabolic `P_B`. It
  inflates `ρ` through the Levi projection, twists by the positive half-modulus
  `T.parabolicHalfModulus B` (`δ_P^(1/2)`, the positive square root of the
  explicit block modulus `δ_P(m) = ∏_(i<j) |det m_i|^(n_j) / |det m_j|^(n_i)`
  of `Group/GL/BlockModulus`), and lets `GL_n(F)` act by right translation on
  the actual space of smooth functions `f` with
  `f(q g) = δ_P(m)^(1/2) ρ(m) f(g)`, where `m` is the Levi part of `q ∈ P_B`.
  The Markdown of `Induction.Parabolic` records the equality of the explicit
  modulus with the Haar module as a separate obligation; this statement does
  not assume it. The carriers of the two inductions are the actual smooth
  function spaces, in `Type (max uF uV)` and `Type (max uF uW)` respectively.
- `HaveSameJordanHolderFactors`
  (`Langlands.Representation.Filtration.ObjectDefinitions`) asserts a common
  length `k`, actual zero-to-full filtrations by subrepresentations of both
  representations with `k` irreducible graded quotients each, a permutation
  `e` of `Fin k`, and an actual `Representation.Equiv` between the `i`-th
  quotient of the first and the `e i`-th quotient of the second. It counts
  multiplicities and allows carriers in independent universes. It is not an
  isomorphism of the inductions and not an identity in a Grothendieck group.

## Scope

- Every rank `n` is included, also `n = 0`. Then the only block shape is the
  empty one, so `B = C`, the Levi and `GL_0(F)` are trivial groups, and a
  finite-length representation is a finite-dimensional space with trivial
  action.
- Zero inducing representations are included; they have length zero.
- `w` is any actual permutation satisfying `ConjugatesLevi`. It need not be a
  minimal coset representative, and it may also permute coordinates inside
  blocks; such internal Weyl factors act on each block group by an inner
  automorphism. A conjugating `w` forces `B` and `C` to have the same number of
  blocks and the same multiset of block sizes (compare the published
  `CuspidalSupport.exists_blockMap_of_conjugatesLevi`), but no relation
  between `B` and `C` is assumed beyond `hw`.
- The finite-length hypotheses concern the whole Levi representations `σ` and
  `τ`. No tensor decomposition of `σ` or `τ` into block representations is
  posited.
- There is no minimality, irreducibility, cuspidality, admissibility, finite
  dimension, countability, unitarity or classification premise, and no
  finite-length premise on the inductions. The conclusion itself asserts
  actual finite composition series of both inductions, so it includes their
  finite length. Finite-length preservation by normalized induction is the
  published statement `Langlands.Parabolic.NormalizedParabolicFiniteLengthStatement`,
  whose proof is task 2a216dfa-5b20-4b4b-9ff8-50b41a0b28f7; it is neither
  assumed nor supplied here.
- The universes `uF`, `uV`, `uW` are independent. The proposition is closed
  over `p`, `F` and `T`, so a proof gives the result for every prime, every
  `p`-adic field and every compatible realization at once.

## Provenance and relation to the literature

The proposition is derived content. It is not printed in this form in either
source below. It is the `GL_n` case of Weyl conjugacy invariance of
normalized induction, written for actual finite-length representations with
actual Jordan–Hölder witnesses instead of Grothendieck groups.

### Ban–Jantzen (2016), Proposition 4.1(3)

D. Ban and C. Jantzen, *The Langlands quotient theorem for finite central
extensions of p-adic groups II: intertwining operators and duality*, Glasnik
Mat. 51(71) (2016), 153–163. Registered source ID
`ban-jantzen-2016-duality`; PDF SHA-256
`7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`, verified by
Worker 757 on 2026-10-31. Worker 757 read printed pp.154, 158 and 163
(one-based PDF pages 2, 6 and 11).

- §2, printed p.154: `G̃` is a finite central extension of the `F`-points of a
  connected reductive group over a nonarchimedean local field `F` of any
  characteristic; `R(G̃)` is the Grothendieck group of smooth finite-length
  representations; "If π1 and π2 have the same irreducible components
  appearing with the same multiplicities, we write π1 = π2. If π1 and π2 are
  actually equivalent as representations, we write π1 ≅ π2." `W = W(G, A)` is
  the Weyl group of a maximal split torus `A`.
- Proposition 4.1(3), printed p.158: for standard Levi factors `M̃`, `L̃`, "If
  M̃ = wL̃w⁻¹ for an element w ∈ W, then i^G̃_M̃ ∘ w = i^G̃_L̃."

For `G = GL_n` (trivial extension), with `A` the diagonal torus, the standard
Levis are the block-diagonal subgroups of block shapes, and `W` is the group of
permutations, represented by permutation matrices. Take `L̃ = B.leviSubgroup`
and `M̃ = C.leviSubgroup`; then `M̃ = wL̃w⁻¹` is `ConjugatesLevi B C w`. The
quoted page does not restate the action of `w` on representations of `L̃`. The
only action producing representations of `M̃ = wL̃w⁻¹` is
`(wσ)(m) = σ(w⁻¹ m w)`, which is `transport` (another representative of the
Weyl element changes it by an inner automorphism of the Levi, hence up to
isomorphism). Evaluated at the class of a finite-length `σ`, the identity says
that `i_C(wσ)` and `i_B(σ)` have the same irreducible components with the
same multiplicities. Since `τ ≅ transport σ` gives `i_C(τ) ≅ i_C(wσ)`, that is
the conclusion here. This statement differs from the source in using actual
composition series instead of `R(G̃)`, in being specific to `GL_n` over
`p`-adic fields, and in making the finite length of the inductions part of
the conclusion.

The printed proof is not an independent input. It reads: "The proof of (3) in
[5] relies on three results: the linear independence of characters, the
Langlands classification, and the geometric lemma of [6] (or [7, Theorem
6.5])." Reference [5] (printed p.163) is J. Bernstein, P. Deligne and
D. Kazhdan, *Trace Paley-Wiener theorem for reductive p-adic groups*, J. Analyse
Math. 47 (1986), 180–192. Because that route uses the Langlands
classification, it cannot serve the intended upstream `GL` classification
route; the later proof of this proposition must replace it by an independent
argument (see Independence below). This statement relies only on the
mathematical content of the identity, not on its printed proof.

### Zelevinsky (1980), Theorem 1.9

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), 165–210.
Registered source ID `zelevinsky-1980-induced-ii`; PDF SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`, verified by
Worker 757 on 2026-10-31. Worker 757 read printed pp.172–174 (one-based PDF
pages 9–11).

- §1.7, printed pp.172–173: `ℛ(G_n)` is the Grothendieck group of
  finite-length representations; "Using tensor products one can identify
  Irr G_α with Irr G_n1 × ... × Irr G_nr"; the product is
  `ρ₁ × ρ₂ = m(ρ₁ ⊗ ρ₂) = i_(n),(k,l)(ρ₁ ⊗ ρ₂)`, and it is associative,
  `(ρ₁ × ρ₂) × ρ₃ = ρ₁ × (ρ₂ × ρ₃) = i_(n),(k,l,m)(ρ₁ ⊗ ρ₂ ⊗ ρ₃)`.
- Theorem 1.9, printed p.174: "The ring ℛ is commutative. In other words if
  π₁ ∈ Alg G_k, π₂ ∈ Alg G_l are of finite length then π₁ × π₂ and π₂ × π₁
  have the same composition factors [i.e. JH⁰(π₁ × π₂) = JH⁰(π₂ × π₁)]."

Theorem 1.9 is the two-block case of this proposition. Take `n = k + l`, the
shape `B = (k, l)`, the reordered shape `C = B.permute e` with `e` the swap of
the two block labels, the canonical block reordering `w = B.blockPermutation e`
with `hw` from `CuspidalSupport.conjugatesLevi_blockPermutation`,
`σ = B.blockTensor (π₁, π₂)` and `τ = C.blockTensor (π₂, π₁)`. The published
`CuspidalSupport.blockPermutationTensorEquiv` is an actual equivalence from
`transport B C w hw σ` to `τ`, and `T.normalizedProductInduced B ρ` is
`T.normalizedParabolicInduced B (B.blockTensor ρ)` by `rfl`
(`Langlands.PadicField.TopologicalData.normalizedProductInduced_eq`). So with `uV = uW`, this proposition implies
the published `Langlands.Parabolic.TwoBlockProductReversalFactors` once one
knows that the external tensor product of two finite-length factors has
finite length as a representation of `GL_k(F) × GL_l(F)`. That fact is not
part of either statement; Ze80 uses the identification of irreducible
representations of `G_α` with tensor products recalled above. Like Ze80, this
proposition does not assert that the induced representations are isomorphic.

The converse direction needs more than Theorem 1.9: this proposition allows any
number of blocks, any finite-length representation of the whole Levi, and any
conjugating permutation, including internal Weyl factors.

## Related Library interfaces

- `Langlands.Parabolic.TwoBlockProductReversalFactors`, proved by the published
  `Langlands.Parabolic.twoBlockProductReversalFactors`, is the two-factor product case
  described above, in one carrier universe and positive ranks.
- `Langlands.CuspidalSupport.AssociatedCuspidalInductionFactorsTheorem` compares
  normalized inductions of associated inducing data only when both are
  irreducible and Levi-cuspidal, in positive rank; it does not cover this
  finite-length whole-Levi assertion.
- `Induction.ConjugateParabolic` compares a parabolic with its actual
  conjugate. It does not change between the standard parabolics `P_B` and
  `P_C` attached to conjugate Levis, which is the content here.

## Proposed proof route (not supplied)

A possible proof first treats irreducible whole-Levi representations: use
actual `p`-adic Levi admissibility and admissible tensor factorization, pass
from two-factor reversal (`twoBlockProductReversalFactors`) to adjacent swaps
by normalized induction in stages and exact factor matching, generate block
permutations by adjacent swaps, and remove internal Weyl factors by actual
transport equivalences. It then uses composition series, exactness of
induction and graded refinement for finite-length whole-Levi data, and treats
rank zero separately. Relevant existing modules include
`CuspidalSupport.IrreducibleLeviAdmissibilityProof`,
`CuspidalSupport.LeviAdmissibleFactorizationProof`,
`CuspidalSupport.BlockPermutation`, `CuspidalSupport.BlockPermutationTensor`,
`CuspidalSupport.AssociationReduction`,
`Parabolic.RefinementInductionTransitivityProof`,
`Parabolic.InductionFiltration` and `Filtration.GradedRefinementProof`. The
existing adjacent-swap assembly has cuspidal hypotheses, so any reuse must
respect its actual scope. This route is a plan only; no theorem is supplied by
this statement.

## Independence

This proposition is a lower prerequisite of analytic segment classification
task aca8805b-054f-4d56-8045-12db7f623404. Its proof must not use, directly or
through proof successors or transitive proof dependencies, the conclusions of:

- analytic segment classification aca8805b-054f-4d56-8045-12db7f623404;
- special-head multisegment exhaustion 3bfb61fa-1129-4fc9-83fd-7fcfec22106e;
- ordered strong-head existence ebea9a8a-9b21-4208-aa31-98c2dea1f8a3;
- quotient coverage 20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584;
- tempered block uniqueness 52e97845-36bb-457d-b76f-70753334b88c;
- `SquareIntegrableLanglandsClassification`,
  1cb45da2-7007-4351-a694-594fb148b8d1;
- square-integrable exhaustion cd8ab97c-0b78-4bce-97c4-d307a28159a4;
- regular exhaustion bf433f0a-921a-428c-b0c0-6475438125ac.

Shared lower results may be reused after an independence check. The proof must
replace the classification-dependent source route of Ban–Jantzen
Proposition 4.1(3).

## Imports

The module imports only `Langlands.Representation.Category.Basic`,
`Langlands.Representation.CuspidalSupport.LeviDefinitions`,
`Langlands.Representation.Filtration.ObjectDefinitions` and
`Langlands.Representation.Induction.Parabolic`. It does not import any
proof input of the planned route.
