# BZ77 4.14(b): the right mixed-product derivative filtration

Authors: Worker 969 (final assembly, the `GL_0` extension, and this audit) and
Worker 723 (the positive-rank proof and the rank dispatch, from their shared
draft). Worker 723 also prepared an independent closure and audit draft. Its
module list agrees with the one below, and its Haar-scaling notes are used in
the section on normalizations.

The theorem `Langlands.Derivative.rightMixedProductDerivativeFiltration` proves
the unchanged published proposition
`Langlands.Derivative.RightMixedProductDerivativeFiltrationStatement.{uF,uV} F T`
from `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement`:

```lean
theorem Langlands.Derivative.rightMixedProductDerivativeFiltration
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T
```

The outer telescope is exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The theorem has no other hypothesis, explicit, implicit or typeclass. The field
universe `uF` and the carrier universe `uV` stay independent. The statement
pair and every pair it imports are unchanged.

## What is proved

Install `T.topology`. For every unitary additive character `ψ`, every `k r d : ℕ`
and `hd : 0 < d ∧ d ≤ (k + r) + 1`, the theorem gives
`e : Fin (rightMixedDerivativeIndices k r d).card ≃ RightMixedDerivativeIndex k r d`
and `IsGluedFrom` for the literal source and the pieces enumerated by `e`.

- Notation: as in BZ77 §3.1 (printed p.450), `P_m` is the mirabolic subgroup of
  `GL_m`. The Library group `mirabolic n` is `P_(n+1)`. The source of the
  mixed product is `mirabolic (k + r) = P_(k+r+1)`. No `P_0` and no
  order-zero mirabolic derivative occurs.
- The source is `rightMixedDerivativeSource T ψ k r d hd`, which is
  `T.rightMixedProductFunctor k r ⋙ mirabolicDerivativeOfOrder T ψ (k+r) d hd ⋙ SmoothRep.toRep`.
  Its domain is the full product category of pairs `(B, A)`, with `B` smooth on
  `mirabolic r` and `A` smooth on `GL_k`, carriers in `uV`. Its values are in
  `Rep.{max uF uV} ℂ (GL_((k+r)+1-d))`.
- The index type `RightMixedDerivativeIndex k r d` is the subtype of the
  published finite set `rightMixedDerivativeIndices k r d`. It contains exactly
  the pairs `(j, t)` with `1 ≤ j ≤ r + 1`, `t ≤ k` and `j + t = d`. Different
  indices stay different even when their grades are zero or isomorphic.
- The grade at `(j, t)` is `rightMixedDerivativePiece T ψ k r d (j, t)`:
  `B^(j) × A^(t)`, that is, the pair of the order-`j` mirabolic derivative and
  the order-`t` `GL` derivative, then the actual
  `binaryNormalizedProductFunctor (r+1-j) (k-t)`, then the published smooth
  rank cast `generalLinearRankCast` along `rightMixedDerivativeIndices_rank`,
  then `SmoothRep.toRep`. The `GL` derivative of order zero is the identity
  functor on its whole input.
- `IsGluedFrom M pieces` (module `Filtration.Definitions`) asks for a
  permutation `σ` and an actual `RepFunctorFiltration` of `M`. That is a chain of
  subfunctors from `0` to `M`, each preserved by every pair of input
  intertwiners, together with natural isomorphisms from its successive
  quotient functors to `pieces ∘ σ`.

So each derivative of `B × A` has a natural finite filtration whose graded
pieces are the functors `B^(j) × A^(t)`, each feasible index exactly once, up
to a permutation. This is not an objectwise, semisimplified or
Grothendieck-group statement.

## The implemented proof

The proof introduces `ψ` and the `GL` rank `k`, then cases on `k`.

```lean
  intro ψ k
  cases k with
  | zero => exact rightMixedProductDerivativeFiltration_zero T ψ
  | succ k =>
    exact RightMixedDerivative.filtration_pos T ψ
      (MirabolicProductMinus.rightPsiCompatibility.{uF, uV} T)
      (MirabolicProductMinus.rightPhiShortExact.{uF, uV} T)
      (leftMixedProductDerivativeIso.{uF, uV} F T)
      (leftMixedProductDerivativeVanishing.{uF, uV} F T)
      (Mirabolic.minusExactness.{uF, max uF uV} F T) k
```

Each branch has exactly the body of the statement at that rank. All five
arguments of the positive branch are published theorems with no hypotheses.
The exactness theorem is used at universes `{uF, max uF uV}`, because the
carriers of the mixed products are in `max uF uV`. Its statement quantifies all
carrier universes, so this is an instance of the published theorem, not an
extra premise.

### `GL` rank zero: the internal arbitrary-carrier extension

`rightMixedProductDerivativeFiltration_zero` is from the published module
`RightMixedProductZeroRank`, which uses the published `ZeroRankTensor`. Their
Markdown describes the declarations. The argument is the following.

- For `k = 0` the inducing subgroup of `B × A` is the whole group
  `mirabolic (0 + r)` (`mem_rightSubgroup_zero`). The character `χ_R` is
  trivial (`rightCharacter_zero_left`), and `GL_0` acts trivially
  (`representation_apply_of_rank_eq_zero`). So evaluation at `1`
  (`Induction.compactInducedTopEquiv`), removal of the trivial twist and
  `id ⊗ ULift.up` give a natural isomorphism
  `B × A ≅ φ^*B ⊗ ULift A`. Here `φ = rightUnitProjection r` is the rank cast
  `mirabolic (0 + r) → mirabolic r` (`rightUnitProjection_eq_castHom`).
  Naturality is checked on both input maps at once.
- `ZeroRankTensor` proves that the actual derivatives commute with a tensor
  factor on which the group acts trivially. On the character quotient the maps
  `[v ⊗ a] ↦ [v] ⊗ a` and back are inverse on generators. They commute with the
  group actions, with both input maps, with pullbacks, with determinant twists
  and with rank casts. Iterating through every `Φ⁻` and the final `Ψ⁻` gives
  `(φ^*B ⊗ ULift A)^(d) ≅ cast(B^(d)) ⊗ ULift A` for every order `d`.
- The only feasible index is `(d, 0)`
  (`rightMixedDerivativeIndices_zero_gl`). Its grade is `B^(d) × A^(0)` with
  `A^(0) = A` by definition. `ZeroRankTensor.binaryRightZeroIso` identifies the
  binary product with a `GL_0` second factor with `B^(d) ⊗ ULift A`.
- The source and the unique grade are therefore naturally isomorphic. The
  one-step filtration `0 ⊆ M` has the single graded piece `M / 0 ≅ M`
  (`RepSubfunctor.quotientNatIsoOfSurjective`), which gives `IsGluedFrom`.

The `GL_0` input `A` keeps its arbitrary complex carrier and its actual
action. It is never replaced by the tensor unit or by a one-dimensional
representation.

### Positive `GL` rank: BZ77's route

`RightMixedDerivative.filtration_pos` is from the published module
`RightMixedProductDerivativePositive` (with the generic
`Filtration.GluedFamily`). Its Markdown describes the declarations. Write
`K = k + 1`. The proof shows that the source is glued from the family of
grades indexed by the finite type, by induction on the mirabolic rank `r`, for
all orders at once.

- Order one. The only index is `(1, 0)`. The order-one mirabolic derivative is
  `Ψ⁻`, the order-zero `GL` derivative is the identity, and the published
  `rightPsiCompatibility` gives `Ψ⁻(B × A) ≅ Ψ⁻B × A` naturally. Whiskering by
  `SmoothRep.toRep` gives a one-step gluing.
- Order recursion. For order `e + 2`, the equalities of functors
  `derivative_succ_eq` and `phiMinus_derivative_eq` peel off the first `Φ⁻`:
  the source is `Φ⁻(B × A)` followed by the order-`(e+1)` derivative and a rank
  cast (`source_succ_eq`). The middle term `rightPhiProduct` of 4.13(c) has this
  cast built in.
- The quotient term. The last term of 4.13(c) is
  `rightPhiQuotient = (Ψ⁻B) × (A|P_K)`, a left mixed product. If
  `e + 1 ≤ K`, the published `leftMixedProductDerivativeIso` gives
  `((Ψ⁻B) × (A|P_K))^(e+1) ≅ Ψ⁻B × (A|P_K)^(e+1)`. Equalities of functors
  identify the right side with the grade at index `(1, e + 1)`, since
  `B^(1) = Ψ⁻B` and `(A|P_K)^(e+1) = A^(e+1)` (`restrictionDerivative_eq`).
  If `e + 1 > K`, the published `leftMixedProductDerivativeVanishing` says that
  the derivative has zero carrier, and the index `(1, e + 1)` is not feasible.
- Mirabolic rank zero (`r = 0`, order `e + 2`). The only index is `(1, e + 1)`.
  `B` lives on `mirabolic 0 = P_1`. The published `rightPhiBoundary` gives
  `rightPhiProduct ≅ rightPhiQuotient` directly. This is 4.13(c) for `τ` on
  `P_1`, where BZ77's convention `P_0 = ∅` removes the first term. The
  Library clause has no `P_0` and no `Φ⁻` on `P_1`. Composed with the quotient
  term this is a natural isomorphism to the only grade.
- Positive mirabolic rank (`r + 1`, order `e + 2`). The published
  `rightPhiShortExact` gives natural transformations
  `i : (Φ⁻B) × A ⟶ Φ⁻(B × A)` and `q : Φ⁻(B × A) ⟶ (Ψ⁻B) × (A|P_K)` whose
  components are injective, exact in the middle and surjective. Whiskering by
  the order-`(e+1)` derivative, a rank cast and `SmoothRep.toRep` keeps them
  short exact. This uses `LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder`
  with the normalized `Ψ⁻` and `Φ⁻` clauses of the published
  `Mirabolic.minusExactness`, and the identity laws for rank casts. The
  subobject is glued by the induction hypothesis at rank `r`, with the grades
  shifted from `(j, t)` to `(j + 1, t)` by `phiMinus_derivative_eq`. The quotient
  is glued from at most one grade, as above. `IsGluedFromFamily.splice` (from
  the published generic splicing in `Filtration.Splicing`) glues the middle
  term from both families. The index bijection `spliceIndexEquiv` sends `(j, t)`
  to `(j + 1, t)` and the quotient grade to `(1, e + 1)`.

Finally `IsGluedFromFamily.exists_equiv` and `Fintype.card_coe` give the
enumeration `e` of the statement. The grades are never altered. Each feasible
pair occurs exactly once, including zero grades and isomorphic grades.

## Boundary cases

- `k = 0`, every `r` and `d`, including `r = 0`, the top order `d = r + 1`, and
  `k = r = 0, d = 1`: the first branch. At the top order the grade is
  `B^(r+1) × A`, the binary product on `GL_0` of the top derivative of `B` and of
  `A` itself, which is the top (order-zero) derivative on `GL_0`. Both actual
  carriers are retained; neither is assumed one-dimensional.
- `r = 0` with `K > 0`: the index set is `{(1, d - 1)}`
  (`rightMixedDerivativeIndices_zero_mirabolic`). Order one uses the `Ψ⁻`
  clause; higher orders use `rightPhiBoundary` and the quotient term with
  `e + 1 = d - 1 ≤ K`.
- Top order `d = (K + r) + 1` with `K > 0`: the index set is `{(r + 1, K)}`
  (`rightMixedDerivativeIndices_top`). In the induction step at rank `r + 1`,
  the quotient index `(1, e + 1)` has `e + 1 = K + r + 1 > K`, so the quotient
  term vanishes by `leftMixedProductDerivativeVanishing`, and the subobject is the
  top-order case at rank `r`. At `r = 0` the only grade is
  `B^(1) × A^(K)`, the binary product on `GL_0` of the two top derivatives,
  with both actual carriers.
- These index equalities are elementary facts about the finite set. They
  identify which grades occur; they prove no filtration.

## Normalizations

All functors are the actual Library constructions with the supplied topology
and character.

- Modulus convention. BZ77 (printed p.444, just before §1.8) defines the
  module of an automorphism `σ` of `U` by
  `∫ f(σ⁻¹(u)) dμ(u) = mod_U(σ) · ∫ f(u) dμ(u)`, and `mod_U(g)` as the
  module of `u ↦ g u g⁻¹`. So `mod_U(σ)` is the scalar by which the image
  of `μ` under `σ⁻¹` differs from `μ`. If the image of `μ` under `σ` is
  `c(σ) · μ` (the pushforward scalar), then `mod_U(σ) = c(σ)⁻¹`. Mathlib's
  `mulEquivHaarChar φ` is the BZ77 module. It satisfies
  `mulEquivHaarChar φ • μ.map φ = μ` (`mulEquivHaarChar_smul_map`), and
  `integral_comap_eq_mulEquivHaarChar_smul` is the displayed formula, since
  `μ.comap φ` is the image of `μ` under `φ⁻¹`.
  Induction (§1.8(a)(1)) uses `mod_U^(1/2)`, the square root of the module
  and so the inverse square root of the pushforward scalar. Localization
  (§1.8(b)) uses `mod_U^(-1/2)`.
- The minus functors `Ψ⁻` and `Φ⁻` are the localizations twisted by
  `|det|^(-1/2)` (normalized `MirabolicMinus`). BZ77 §3.2 defines
  `Ψ⁻ = r_{V,1}` and `Φ⁻ = r_{V,θ}`, and §1.8(b) twists `r_{U,θ}` by
  `mod_U^(-1/2)`. The published theorem
  `Langlands.mirabolicRadicalHaarModulus` (`Group.GL.MirabolicModulusProof`)
  proves that the actual Haar character `HaarModulus.normalizerCharacter`
  (Mathlib's `mulEquivHaarChar` of `u ↦ g u g⁻¹`, that is, the BZ77
  `mod_U(g)`) on the mirabolic radical is the determinant norm. The 4.13(c)
  proofs use it through `mulEquivHaarChar_conj_levi_inv`
  (`MirabolicProductMinusRightBoundary`).
- The right mixed product (BZ77 §4.12(III), printed p.457) is
  `i_{U,1} ∘ ε`: the compactly supported induction of §1.8(a), which carries
  `mod_U^(1/2)`, after a twist by the separate character
  `ε(p, a) = ν_k(a)^(-1/2)`. The Lean twist is
  `χ_R = rightRectangleHalfCharacter · rightEpsilonCharacter`
  (`rightLeviCharacter_eq_mul` in `Mirabolic.MixedProducts`), where
  `rightEpsilonCharacter` is this `ε`. At `k = 0`, `χ_R = 1`
  (`rightCharacter_zero_left`). At `r = 0` and `k > 0`,
  `χ_R(p, a) = ν_k(a)^(-1/2) = ε(p, a)` is retained.
- The rectangle factor `rightRectangleHalfCharacter` is
  `|det d|^(k/2) |det a|^(-r/2) = D^(1/2)`, where
  `D = |det d|^k / |det a|^r` and `d = Mirabolic.projection p` is the
  upper-left `r × r` block of `p`. The published
  `HarmonicAnalysis.padicRectangularHaarScalingStatement` (in the closure)
  proves that the image of an additive Haar measure `μ` on `r × k` matrices
  under `σ : X ↦ d X a⁻¹` is `c · μ`, with pushforward scalar `c = D⁻¹`.
  The same theorem for `σ⁻¹ : X ↦ d⁻¹ X a` gives the scalar `D`. So the BZ77
  module of `σ` is `mod_U(σ) = D = c⁻¹`. The rectangle factor
  `D^(1/2) = c^(-1/2)` is the square root of this module, which is the
  `mod_U^(1/2)` of §1.8(a)(1). It is the inverse square root of the
  pushforward scalar `c`, not its square root. The factor `ε` is not part of
  the module.
- The binary normalized product uses the half modulus of the block parabolic
  (`parabolicHalfModulus` of the binary shape). It is the positive square root
  `leviHalfModulus = leviModulus^(1/2)` (`leviHalfModulus_apply`) of the
  determinant formula `leviModulus` of `Group.GL.BlockModulus`, pulled back
  through the Levi projection. The published theorem
  `Langlands.glBlockModulusHaar` (`Group.GL.BlockModulusHaarProof`, not
  imported here) proves that the image of a Haar measure on the block
  unipotent radical under Levi conjugation `u ↦ m u m⁻¹` is
  `leviModulus(m)⁻¹` times that measure. So `leviModulus` is the BZ77 module
  `mod_U`, and `parabolicHalfModulus` is the `mod_U^(1/2)` of §1.8(a)(1).
- Read with these Haar facts, the determinant characters of `χ_R` and of the
  binary product agree with BZ77's Haar-modulus normalizations. This reading
  is a correspondence check only: the Lean proof uses the characters as
  defined, and the comparisons it needs are those of the next item.
- The comparisons between these determinant characters and the Haar moduli
  that occur in the 4.13(c) computations are proved in the published proofs of
  `rightPsiCompatibility`, `rightPhiBoundary` and `rightPhiShortExact`. They
  compute the actual Haar ratio of each split-stages comparison (`|det D|`, or
  `|det a|`) and prove the real-power identities between the source twist, the
  `χ_R` of the relevant shapes, the minus normalizations and the binary half
  modulus (for example `rightPsi_scalar_eq`). No residual twist is assumed. The
  4.14(a) proof composes published comparisons of the same kind.
- The assembly in this module, the order recursion and the splicing add no
  character. In rank zero the trivial `χ_R`, the trivial `GL_0` action and the
  commutation of every twist with the inert factor are proved in
  `RightMixedProductZeroRank` and `ZeroRankTensor`.

## Original source and provenance

The registered original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
relevant passages are:

- the definition of the module just before §1.8, printed p.444 (PDF p.5):
  `∫ f(σ⁻¹u) dμ(u) = mod_U σ · ∫ f(u) dμ(u)`, with `mod_U(g)` the module of
  `u ↦ g u g⁻¹`;
- §§1.8–1.9, printed pp.444–445 (one-based PDF pp.5–6): normalized induction,
  with `mod_U^(1/2)` in §1.8(a)(1), and localization, with `r_{U,θ}` twisted
  by `mod_U^(-1/2)` in §1.8(b); Proposition
  1.9(g), that `i_{U,θ}` and `r_{U,θ}` commute with `★ ↦ ★ ⊗ τ` for a
  representation `τ` of another group;
- §§1.10–1.11, printed p.445 (PDF p.6): subfunctors are taken objectwise and
  preserved by all morphisms, and "glued from" means a filtration whose
  quotients agree with the given objects after a permutation;
- §§3.1–3.5, printed pp.450–452 (PDF pp.11–13): `P_m`, the minus functors and
  the derivatives `τ^(k) = Ψ⁻(Φ⁻)^(k-1)τ`;
- §§4.1–4.3, printed p.454 (PDF p.15): products of `GL` representations and
  the derivatives `π^(0) = π`, `π^(k) = (π|P)^(k)`;
- §4.12, printed pp.456–458 (PDF pp.17–19): the products `i = i_{U,1} ∘ ε`,
  with case (III) (`M_1 = P_m`, `M_2 = G_k`, `G = P_n`) and its twist
  `ε(m_1, m_2) = ν(m_2)^(-1/2)` (p.457);
- Proposition 4.13(c) and Corollary 4.14, printed p.458 (PDF p.19).

Corollary 4.14(b) states that for `τ` on `P_m` and `ρ` on `G_k`, `(τ × ρ)^(i)`
is glued from `τ^(j) × ρ^(i-j)`, `j = 1, …, i`. Its proof says that (b) follows
from (a) and 4.13(c). Proposition 4.13 assumes `P_0 = ∅` and `ρ|P_0 = 0`.
The derivatives beyond the rank are zero; the published index family omits
those pairs instead, and the proof shows that the corresponding quotient term
is zero. The positive-rank proof follows this route, with 4.13(c) and 4.14(a)
entering only through their published proofs.

The `k = 0` case is internal: the source does not treat a `GL_0` factor
separately. It is the direct identification described above, based on
Proposition 1.9(g); it does not use the source's route through 4.13(c). The
order recursion, the rank casts and the splice bookkeeping are also internal
derived content. Text extraction loses some symbols on these pages; the cited
statements were checked against the page images. A bounded search of the
project's literature and notes found no applicable BZ77 erratum; this is not a
claim that none exists.

## Published inputs

Every theorem input has an independently accepted and published proof whose
approving review carries no reviewer qualification. Each was fetched and
checked against the Library.

| Lean input | Content | Artifact and publication |
| --- | --- | --- |
| `RightMixedProductDerivativeFiltrationStatement` | target proposition | `cb1dceb1`, commit `7114a390` |
| `rightMixedProductDerivativeFiltration_zero` | `k = 0` extension | `114a6ef1`, commit `8415f617` |
| `ZeroRankTensor` | inert tensor factor commutations | `2057375a`, commit `9a8ca758` |
| `RightMixedDerivative.filtration_pos`, `Filtration.GluedFamily` | positive-rank filtration | `9487e57e`, commit `8f53f05b` |
| `MirabolicProductMinus.rightPsiCompatibility` | 4.13(c), `Ψ⁻` clause | `424f4227`, commit `cb42061b` |
| `MirabolicProductMinus.rightPhiShortExact` | 4.13(c), `Φ⁻` sequence | `5449db58`, commit `00315d47` |
| `MirabolicProductMinus.rightPhiBoundary` | 4.13(c) at `P_1` | `58a3c341`, commit `b22e1857` |
| `leftMixedProductDerivativeIso`, `leftMixedProductDerivativeVanishing` | 4.14(a) | `e99bbe1b`, Reviewer 7469, commit `b4b4160d` |
| `Mirabolic.minusExactness` | exactness of the minus functors | `d307cd07`, commit `9a8ca758` |
| `Filtration.Splicing.Basic`, `Filtration.Splicing` | generic natural splicing, refinement | `52641b38`, commit `26e9adf3`; `fe5fbc72`, commit `6cb15022` |
| `LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder`; `mapsShortExact_id`, `mapsShortExact_comp` (`ShortExactFunctorLaws`) | composition of exact functors | `LevelCalculus`: `e85cf101`, commit `5e4a58e8`, and `6ded142e`, commit `7114a390`; `ShortExactFunctorLaws` was extracted unchanged from `LevelCalculus` at integration |
| `mirabolicDerivativeDetection` | BZ77 §3.5 detection (imported by `LevelCalculus`) | `3ace613e`, commit `81727e81` |

The minus-exactness proof is the published proof of task `b65bc667`. It was
reused by its Lean name only. Its author's operator pause is untouched; the
author was not contacted.

## Complete import and proof-dependency audit

The project import closure has 302 modules besides this entry, listed below,
and 129 directly encountered external (Mathlib and core) imports. It
consists of the 260 modules of the 4.14(a) proof's closure, including that
entry, and 42 further modules. All 604 Lean and Markdown files of
the closure are nonempty and byte-identical to Library commit
`04247de81e81d501f4b57b138c70ba2d5b16e793`. They are unchanged since
`b4b4160d118213b51ef28eb814f1828ac3902ada`. The only
new pair is this entry. No proposition definition, citation, draft, pending
task or consumer conclusion supplies a proof.

Reviewer 7469 independently traversed the 4.14(a) closure (the same 260
modules) and checked it against the same exclusion conditions, inspecting the
broad scan matches and the relevant lower bodies. The scans below cover the
whole closure again. For the modules beyond the 4.14(a) closure, the
mathematical content is as follows.

| Modules | Content and provenance |
| --- | --- |
| `RightMixedProductZeroRank`, `Filtration.OneStep` (with `ZeroRankTensor` and `Filtration.QuotientFirstIso`, which are also in the 4.14(a) closure) | The `GL_0` comparison described above: evaluation at `1`, explicit inverse tensor/quotient maps, one-step filtration. No positive-rank compatibility, exactness or consumer result. |
| `RightMixedProductDerivativePositive`, `Filtration.GluedFamily`, `Splicing`, `Splicing.Basic`, `QuotientTail`, `IsoTransport`, `Precomposition`, `Transport` | Equalities of functors after `subst`, index arithmetic, and generic natural splicing of filtrations along a short exact sequence of functors. The mathematical inputs are exactly the five published theorems and `rightPhiBoundary`. |
| `MirabolicProductMinusRightPsi`, `…RightPsiZero`, `…RightPsiGroups`, `…RightPsiCoefficient` | The `Ψ⁻` clause: radical coinvariants of compact induction by the published split-stages comparison, actual Haar ratio, coefficient tensor quotient, positive binary product. |
| `MirabolicProductMinusRightPhi`, `…RightPhiAssembly`, `…RightPhiCycle*`, `…RightPhiIdentity*`, `MirabolicPhiMinusMackey`, `MirabolicPlus` | The `Φ⁻` sequence: two-orbit Mackey restriction sequence through the plus subgroup, the cycle and identity pieces computed by split-stages comparisons, exactness of the character localization from the published `Jacquet.Localization.characterLocalizationExactness`. `MirabolicPlus` contains only the construction laws of the plus functors; no plus-functor exactness or adjunction is used. |
| `MirabolicProductMinusRightBoundary`, `Induction.SplitKernelCharacter` | The `P_1` boundary: character-twisted integration over a split kernel and `mulEquivHaarChar_conj_levi_inv`. |
| `MirabolicMinusExactnessProof`, `…Statement`, `Group.GL.UpperUnipotentCompactContainment*`, `RankinSelberg.UnipotentUnimodularity` | Exactness of the four minus functors: `characterLocalizationExactness` for a radical in which every compact set lies in a compact subgroup, shown by compact containment in the upper unipotent group. |
| `LevelCalculus`, `ShortExactFunctorLaws`, `Category.Abelian`, `MirabolicDerivativeDetection*`, `MirabolicDerivativeVanishing` | `LevelCalculus` collects elementary consequences of the definitions of level and homogeneity. Its artifacts `e85cf101` and `6ded142e` are conditional helpers for the Ze80 6.2 homogeneity task `b711af72`, which is not an excluded task; none of that task's classification modules is in the closure. Only `mapsShortExact_mirabolicDerivativeOfOrder` (through `mapsShortExact_mirabolicRankCast`, `mapsShortExact_phiMinusIterate` and `mapsShortExact_mirabolicDerivative`) is used, with `mapsShortExact_id` and `mapsShortExact_comp` from `ShortExactFunctorLaws`. These compose the exactness clauses passed to them. They use neither detection nor any level or homogeneity result. `LevelCalculus` imports the published §3.5 detection proof (`3ace613e`), which applies `derivativeDetection` from `MirabolicDerivativeVanishing` (Worker 1024, for BZ77 3.8, task `a925b519`); that module rests on `MinusVanishing`. `Category.Abelian` proves that smooth representations form an abelian category. |
| `Mirabolic.LeftMixedProductSuccessor` | Elementary group and determinant facts about the case (II) subgroup, written for a Ze80 §5.3 embedding. Only `determinantNorm_leftSubgroup` is used, in `…RightPhiIdentityGroups`. It imports only `MirabolicCharacter`, `MixedProducts` and `Parabolic.QuotientCompactProof`. |
| `Group.GL.BlockDeterminant`, `Analysis.Local.CompactOpenCoverUnimodularity*` | The determinant of a block parabolic element, and two-sided Haar invariance for groups covered by compact open subgroups. |
| `RightMixedProductDerivativeFiltrationStatement` | The target definitions and elementary index lemmas, unchanged. |

Artifact provenance check. Each closure file was matched against the
published artifact records. Eight closure modules have no artifact record of
their own: `Group.GL.RankReindex`, `HarmonicAnalysis.PadicLatticeTopology`,
`Compact.OrbitMeanTranslation`, `Derivative.MirabolicDeterminant`,
`Derivative.ShortExactFunctorLaws`, `OrbitSpan`, `Tensor.OneFactor` and
`Topology.CompactNormCharacter`. Their Markdown states that their declarations
were collected, moved or extracted unchanged from already reviewed modules,
mostly during integration. They are covered by the same scans.

Two records that ship closure files mention an identifier from the exclusion
sections of the contract.

- The record of `Derivative.MinusVanishing` (artifact `c6026915`) calls it an
  internal helper for task `2e5183b1`. That is the upstream derivative proof
  task whose restriction sections this contract copies verbatim, not an
  excluded conclusion. The module proves only the consequence of BZ77 3.2(e)
  that `Ψ⁻X = Φ⁻X = 0` forces `X = 0`, by a direct character-averaging
  argument, and it imports no excluded module. The closure uses only its
  elementary lemmas: `MirabolicProductMinusRightBoundary` uses the compact
  lattice-box subgroups of the radical (`radicalBox`, `isCompact_radicalBox`,
  `mem_radicalBox`, `exists_mem_latticeBox`), and
  `MirabolicProductRestrictionOrbits` uses `exists_lastRow_eq_of_ne_zero`
  (an invertible matrix with a prescribed nonzero last row). The vanishing
  theorem itself is used only by `MirabolicDerivativeVanishing`, which the
  §3.5 detection proof imported by `LevelCalculus` applies, and this proof
  does not use detection.
- The publication of the excluded `SupercuspidalCoinvariantFinitenessProof`
  (task `62de5903`, artifact `001944f3`, commit `333fb398`) lists
  `MirabolicDerivativeVanishing` (both files) and `Mirabolic/MixedProducts.md`
  among its snapshot files. `MirabolicDerivativeVanishing` was published
  earlier at commit `2b8beb8b` by the BZ77 3.8 artifact `f957ae76`
  (Worker 1024). The bytes of all three files are the same at `2b8beb8b`, in
  the commit before `333fb398`, in `333fb398` and in the current Library. The
  imports of `MirabolicDerivativeVanishing` (`MinusVanishing`,
  `MirabolicDerivativeDetectionStatement`) contain no Whittaker finiteness
  module. So these mentions are snapshot listings, not dependencies.

## Exclusion audit, condition by condition

Each row excludes the named conclusions, their proof successors and their
transitive consequences. The findings rest on the content audit above as well
as on the name and identifier scans described after the tables.

### Shared upstream scope

| Condition | Finding |
| --- | --- |
| `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, all-character single-block task `62de5903-b616-4b5c-88eb-a066b77c5467`, successors and consequences | Not used. Its proof module is not in the closure; the record mentions are explained above. Compact averaging in the lower induction modules is a direct local construction. |
| No consumer assumption replaces a missing general derivative or tensor proof | Every derivative, exactness and tensor input is a published proof (table above). The theorem has no hypothesis. |
| Worker 127's operator pause | Kept. Worker 127 was not contacted or woken; the published minus-exactness proof is used by name only. |
| `GenericSegmentProductUniqueness`, `30341ae4-65f2-4a0e-9283-763db01a409e` | No genericity or segment-uniqueness input. |
| Multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`; ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | No exhaustion or head-existence input. |
| Quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; ordered conversion `8252833d-c269-41a9-824c-5879e531b23b` | No coverage or conversion input. The quotients used are module quotients by relation spans and subfunctors. |
| Tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c` | No tempered input. |
| `SquareIntegrableLanglandsClassification`, `1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`; regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac` | No classification, square-integrability or exhaustion input. |

### Independence (binding sections of task `2e5183b1` revision 2)

| Condition | Finding |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; tasks `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Not used. This theorem is an upstream input of those proofs, and none of their modules is in the closure. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and successors | No juxtaposed-product or quotient-homomorphism input. |
| `SegmentSocleProductIrreducibility`, `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | No segment-product irreducibility input. |
| `AdjacentUnlinkedSegmentSocleSwap`, `e3634665-571b-4852-9f4c-bab8a1053434`, successor `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | No socle swap. The tensor swaps in the `GL_0` case are linear algebra. |
| `TwoSegmentSocleCommutation`, `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No commutation input. |
| `LinkedSegmentSocleGluing`, `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | No segment gluing. The gluing here is the generic natural splicing of filtrations. |
| `OrderedMultisegmentSocleExistence`, `23189526-80b0-4828-a6d4-7ebec2cbeef5`; socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No socle existence or exhaustion. |
| Segment analytic classification `aca8805b-054f-4d56-8045-12db7f623404` | No segment or analytic classification. |
| Special-head exhaustion `3bfb61fa-…`, ordered special-head existence `ebea9a8a-…`, quotient coverage `20e4e1c6-…`, ordered conversion `8252833d-…`, tempered uniqueness `52e97845-…`, `GenericSegmentProductUniqueness` `30341ae4-…`, `SquareIntegrableLanglandsClassification` `1cb45da2-…`, exhaustions `cd8ab97c-…`, `bf433f0a-…` | As in the first table. |
| Forward special-segment essential square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No square-integrability input. |
| `SegmentHeadProductIrreducibility`, `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | No head criterion. |
| Shared lower inputs (derivative functors, exactness, Leibniz filtration, geometric lemma, cuspidal support, finite length) only after an independence check | The derivative functors, exactness and the 4.13(c)/4.14(a) inputs are checked above. No Leibniz filtration, geometric-lemma consumer, cuspidal-support theorem or finite-length theorem is used. `Category.Basic` defines finite length and proves nothing about it here. |

### Additional BZ77-only restrictions

| Condition | Finding |
| --- | --- |
| Every segment derivative formula, segment-socle/head existence or Jacquet formula, segment classification; (b), (d), (e), (f) of the parent six-statement contribution and proofs depending on them | None is used. The derivatives here are the general BZ77 functors. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; `TwoSupercuspidalProductStructure`, `ab61f565-1427-4746-ba77-46097563e962` | Not used. `Classification.Supercuspidal`, `SupercuspidalContragredientAux` and `SupercuspidalContragredientStatement` are in the closure through `Smooth.SmallRealizationProof`. They supply predicates, class packaging, equivalence invariance and a conditional duality interface, and no product theorem. |
| Individual special-head/reverse-socle existence `67279e36-f3c2-42e3-9302-11729784042e`; individual segment-socle/reverse-head existence `4ca79bbd-589e-476b-9f65-661e799984b5` | No existence input. |
| `SegmentSpecialEssentialSquareIntegrability`, `5eece9e8-…`; `aca8805b-…`; `3bfb61fa-…`; `ebea9a8a-…`; `20e4e1c6-…`; `8252833d-…`; `52e97845-…`; `1cb45da2-…`; `cd8ab97c-…`; `bf433f0a-…`; `8364e73f-…`; `30341ae4-…`; `23189526-…`; `MultisegmentSocleExhaustion` `f3a69bc8-…`; `2ae5cbe5-…`; `e3634665-…` | As in the tables above. |
| `SegmentFullJacquetFormula`, `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its exact proof successor; `SegmentHeadJacquetFormula`, `55ad1e10-62d8-46b7-a081-909ef0056426`; `SegmentSocleJacquetFormula`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`; `SegmentSpecialJacquetExponentNormFormula`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | No segment Jacquet formula. The localizations computed are general radical coinvariants of compact inductions. |
| Ze80 §3.5 and §9.6 segment derivative formulas | Not used. |
| No derivative result without a proof accepted and published under these conditions | Every derivative input is in the table of published inputs. |
| Ze80 4.2 or 9.7 product criteria, Ze80 9.3, any classification or exhaustion theorem; no circular use of the Ze80 4.2 converse for Proposition 1.11 | None is used. |
| Only fully proved, independently accepted and published BZ77 general derivative inputs; the other proposition definitions of a statement module authorize nothing | The 4.13(c) and 4.14(a) clauses enter only through their published proofs. Other proposition definitions in the imported statement modules are not used as proofs. |

### Whittaker-finiteness independence

| Condition | Finding |
| --- | --- |
| `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`, parent `5ab445dc-d2b4-4072-80d1-6370870a4a26` | Not used. |
| `LeviCuspidalCoinvariantFinitenessStatement`, proof task `3ff5c8fb-397c-4345-bcb3-5d98a0993d18` | Not used. |
| Mirabolic finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa` | Not used. No mirabolic finite-length result is in the closure. |
| Worker 288's all-character and degenerate-character adapters | Not used. The lower Whittaker modules in the closure supply characters, matrix coefficients and quotient integration only. |

### Ownership

The 4.13(a), 4.13(b,c), 4.13(d), 4.14(a), 4.14(c), splicing and
exact-transport units are reused only through their published Library results
and are not duplicated. Ownership pointers grant no hypothesis.

### Scans

- No identifier among the 38 task and artifact identifiers in the
  exclusion sections of the contract occurs in any Lean file of the closure.
- An exact-name scan of all closure Lean files for the excluded declarations
  (segment-socle, segment-head, two-supercuspidal, Jacquet-formula,
  classification, exhaustion and coinvariant-finiteness names) finds only the
  three `Classification.Supercuspidal…` modules discussed above.
  `Jacquet.CharacterAveraging` has a `section Exhaustion` (exhaustion of a
  compact group by open subgroups), and `Parabolic.GeometricPrerequisitesStatement`
  defines `UnipotentExhaustionClause`, a proposition about unipotent groups.
  A broader scan of the further modules finds only the homogeneity
  definitions used by `LevelCalculus`.
- No closure Lean file contains `sorry`, `admit`, an `axiom` declaration,
  `native_decide`, `implemented_by`, `extern`, `run_cmd` or `#eval`. The entry
  depends only on `propext`, `Classical.choice` and `Quot.sound`.

These scans support the content audit; they do not replace it.

## Complete project import closure

All direct and transitive project imports, excluding this entry. The Lean and
Mathlib commits of the environment are `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`
and `5ed2965256430c3649e86755f9576b54eca72435`.

```text
Analysis.Local.CompactOpenCoverUnimodularityProof
Analysis.Local.CompactOpenCoverUnimodularityStatement
Analysis.Local.ModularCompactAverage
Analysis.Local.QuotientAutomorphismProof
Analysis.Local.QuotientAutomorphismStatement
Analysis.Local.QuotientAverageReal
Analysis.Local.QuotientAveragingKernel
Analysis.Local.QuotientComplex
Analysis.Local.QuotientFunctional
Analysis.Local.QuotientMass
Analysis.Local.QuotientMeasure
Analysis.Local.QuotientMeasureExistence
Analysis.Local.QuotientMeasureExistenceStatement
Analysis.Local.QuotientMeasurePrerequisites
Analysis.Local.QuotientPositiveLifting
Analysis.Local.QuotientTopology
Analysis.Local.QuotientTranslation
Analysis.Local.SplitKernelQuotient
Group.GL.Basic
Group.GL.BlockDeterminant
Group.GL.BlockModulus
Group.GL.Blocks
Group.GL.CompactOpen
Group.GL.CountabilityProof
Group.GL.CountabilityStatement
Group.GL.Maps
Group.GL.Mirabolic
Group.GL.MirabolicMixedOrbitCoverageProof
Group.GL.MirabolicMixedOrbitCoverageStatement
Group.GL.MirabolicMixedOrbitData
Group.GL.MirabolicMixedOrbitRadicals
Group.GL.MirabolicMixedOrbitSectionCoefficients
Group.GL.MirabolicMixedOrbitSections
Group.GL.MirabolicMixedOrbitSpecializations
Group.GL.MirabolicMixedOrbitStages
Group.GL.MirabolicMixedProductSubgroups
Group.GL.MirabolicModularCharacterProof
Group.GL.MirabolicModularCharacterStatement
Group.GL.MirabolicModulusProof
Group.GL.MirabolicModulusStatement
Group.GL.MirabolicOppositeIntersection
Group.GL.MirabolicProjection
Group.GL.MirabolicRadical
Group.GL.Nonarchimedean
Group.GL.NonarchimedeanStatement
Group.GL.NormalizedCharacter
Group.GL.OppositeBlocks
Group.GL.Padic
Group.GL.PadicBlocks
Group.GL.PadicOppositeBlocks
Group.GL.PadicUpperUnipotent
Group.GL.RankMaps
Group.GL.RankReindex
Group.GL.ReverseBlocks
Group.GL.TriangularParabolic
Group.GL.UpperUnipotent
Group.GL.UpperUnipotentCompactContainmentProof
Group.GL.UpperUnipotentCompactContainmentStatement
Group.HaarModulus
HarmonicAnalysis.AlgebraicIntegral
HarmonicAnalysis.AlgebraicIntegrand
HarmonicAnalysis.Basic
HarmonicAnalysis.Conductor
HarmonicAnalysis.HaarConjugacy
HarmonicAnalysis.PadicAdditiveConductorProof
HarmonicAnalysis.PadicHaarScalingStatement
HarmonicAnalysis.PadicLatticeTopology
HarmonicAnalysis.PadicRectangularHaarScalingProof
HarmonicAnalysis.PadicScalarHaarScalingProof
LocalFactor.Harmonic.Statement
LocalField.Canonical
LocalField.Definitions
LocalField.Normalization.Definitions
LocalField.Normalization.Proof
LocalField.Normalization.Statement
LocalField.Topology
Representation.Category.Abelian
Representation.Category.Basic
Representation.Category.Subquotients
Representation.Category.Twist
Representation.Classification.Supercuspidal
Representation.Classification.SupercuspidalContragredientAux
Representation.Classification.SupercuspidalContragredientStatement
Representation.Compact.Definitions
Representation.Compact.FiniteMean
Representation.Compact.OrbitMeanTranslation
Representation.Compact.ProjectionProof
Representation.Compact.ProjectionStatement
Representation.Compact.SurjectivityProof
Representation.Compact.SurjectivityStatement
Representation.Conductor.Congruence
Representation.Derivative.Homogeneity
Representation.Derivative.Iteration
Representation.Derivative.LeftMixedProductDerivativeProof
Representation.Derivative.LeftMixedProductHigher
Representation.Derivative.LeftMixedProductVanishing
Representation.Derivative.LeftMixedProductZeroRank
Representation.Derivative.LevelCalculus
Representation.Derivative.MinusVanishing
Representation.Derivative.MirabolicCharacter
Representation.Derivative.MirabolicDerivativeDetectionProof
Representation.Derivative.MirabolicDerivativeDetectionStatement
Representation.Derivative.MirabolicDerivativeVanishing
Representation.Derivative.MirabolicDeterminant
Representation.Derivative.MirabolicLatticeBox
Representation.Derivative.MirabolicMinus
Representation.Derivative.MirabolicMinusExactnessProof
Representation.Derivative.MirabolicMinusExactnessStatement
Representation.Derivative.MirabolicMixedOrbitCharacters
Representation.Derivative.MirabolicPhiMinusMackey
Representation.Derivative.MirabolicPlus
Representation.Derivative.MirabolicProductMinusBoundary
Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Representation.Derivative.MirabolicProductMinusLeftPhi
Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison
Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison
Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
Representation.Derivative.MirabolicProductMinusLeftPhiLocalization
Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization
Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Representation.Derivative.MirabolicProductMinusLeftPhiSection
Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Representation.Derivative.MirabolicProductMinusLeftPsi
Representation.Derivative.MirabolicProductMinusLeftPsiInduction
Representation.Derivative.MirabolicProductMinusPhiKernelComparison
Representation.Derivative.MirabolicProductMinusRightBoundary
Representation.Derivative.MirabolicProductMinusRightPhi
Representation.Derivative.MirabolicProductMinusRightPhiAssembly
Representation.Derivative.MirabolicProductMinusRightPhiCycle
Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient
Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups
Representation.Derivative.MirabolicProductMinusRightPhiIdentity
Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
Representation.Derivative.MirabolicProductMinusRightPsi
Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
Representation.Derivative.MirabolicProductMinusRightPsiGroups
Representation.Derivative.MirabolicProductMinusRightPsiZero
Representation.Derivative.MirabolicProductRestrictionFactors
Representation.Derivative.MirabolicProductRestrictionMackey
Representation.Derivative.MirabolicProductRestrictionOrbits
Representation.Derivative.MirabolicProductRestrictionTransport
Representation.Derivative.MixedProductDerivativeStatement
Representation.Derivative.MixedProductRankCast
Representation.Derivative.OrderRecursion
Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
Representation.Derivative.RightMixedProductDerivativePositive
Representation.Derivative.RightMixedProductZeroRank
Representation.Derivative.ShortExactFunctorLaws
Representation.Derivative.ZeroRankTensor
Representation.Dual.Definitions
Representation.Filtration.Definitions
Representation.Filtration.GluedFamily
Representation.Filtration.IsoTransport
Representation.Filtration.OneStep
Representation.Filtration.Precomposition
Representation.Filtration.QuotientFirstIso
Representation.Filtration.QuotientTail
Representation.Filtration.Splicing
Representation.Filtration.Splicing.Basic
Representation.Filtration.Transport
Representation.Geometric.ClosedSubgroupAssembly
Representation.Geometric.ClosedSubgroupDefinitions
Representation.Geometric.ClosedSubgroupMackeyProof
Representation.Geometric.ClosedSubgroupStatement
Representation.Geometric.CompactOrbitRestriction
Representation.Geometric.CosetAction
Representation.Geometric.CosetOrbitHomeomorph
Representation.Geometric.OrbitRestriction
Representation.Geometric.OrbitSectionExtensionProof
Representation.Geometric.OrbitSectionExtensionStatement
Representation.Induction.BinaryPositiveCompact
Representation.Induction.BinaryProduct
Representation.Induction.BlockFactors
Representation.Induction.CharacterTwistProof
Representation.Induction.CompactAutomorphism
Representation.Induction.CompactAutomorphismIntegralProof
Representation.Induction.CompactAutomorphismIntegralStatement
Representation.Induction.CompactCoinvariantBijectivityProof
Representation.Induction.CompactCoinvariantBijectivityStatement
Representation.Induction.CompactCoinvariantIntegral
Representation.Induction.CompactCoinvariantLocalInverseProof
Representation.Induction.CompactCoinvariantLocalInverseStatement
Representation.Induction.CompactLocalSection
Representation.Induction.CompactLocalSectionSpanningProof
Representation.Induction.CompactLocalSectionSpanningStatement
Representation.Induction.CompactLocallyConstant
Representation.Induction.CompactQuotientCutoff
Representation.Induction.CompactQuotientProof
Representation.Induction.CompactSurjectivityProof
Representation.Induction.CompactSurjectivityStatement
Representation.Induction.CompactTransitivityProof
Representation.Induction.CompactTransitivityStatement
Representation.Induction.Definitions
Representation.Induction.InverseTranspose
Representation.Induction.NormalCoinvariantKernelProof
Representation.Induction.NormalCoinvariantKernelStatement
Representation.Induction.NormalCoinvariantMap
Representation.Induction.NormalCoinvariantProof
Representation.Induction.NormalCoinvariantStatement
Representation.Induction.NormalSplitComparison
Representation.Induction.OppositeParabolic
Representation.Induction.Parabolic
Representation.Induction.SplitKernelCharacter
Representation.Induction.SplitKernelCharacterExtension
Representation.Induction.SplitKernelCompact
Representation.Induction.SplitKernelCovariance
Representation.Induction.SplitKernelEquivariant
Representation.Induction.SplitKernelHaarTrivial
Representation.Induction.SplitKernelIntegral
Representation.Induction.SplitKernelLocalizationData
Representation.Induction.SplitKernelSectionAction
Representation.Induction.SplitQuotientProof
Representation.Induction.SplitQuotientStatement
Representation.Induction.SplitStagesCharacterComparison
Representation.Induction.SplitStagesCharacterComparisonStatement
Representation.Induction.SplitStagesCharacterIntegrand
Representation.Induction.SplitStagesComparison
Representation.Induction.SplitStagesRetraction
Representation.Induction.StructuralStatement
Representation.Induction.SurjectivityProof
Representation.Induction.SurjectivityStatement
Representation.Jacquet.CharacterAveraging
Representation.Jacquet.Coinvariants
Representation.Jacquet.ExactProof
Representation.Jacquet.ExactStatement
Representation.Jacquet.Localization
Representation.Jacquet.LocalizationExactnessProof
Representation.Jacquet.LocalizationExactnessStatement
Representation.Jacquet.LocalizationTransport
Representation.Jacquet.PositiveCharacter
Representation.Jacquet.SmoothTwist
Representation.MatrixCoefficient.Definitions
Representation.MatrixCoefficient.LawsProof
Representation.MatrixCoefficient.LawsStatement
Representation.Mirabolic.LeftMixedProductSuccessor
Representation.Mirabolic.MixedProducts
Representation.OrbitSpan
Representation.Parabolic.GeometricPrerequisitesStatement
Representation.Parabolic.QuotientCompactProof
Representation.RankinSelberg.GeneralLinearUnimodularity
Representation.RankinSelberg.LastRowCompactOrbitProof
Representation.RankinSelberg.LastRowCompactOrbitStatement
Representation.RankinSelberg.Measures
Representation.RankinSelberg.QuotientIntegrals
Representation.RankinSelberg.UnimodularityStatement
Representation.RankinSelberg.UnipotentUnimodularity
Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Representation.Smooth.Admissibility.CofinalProof
Representation.Smooth.Admissibility.CofinalStatement
Representation.Smooth.Admissibility.EquivalenceProof
Representation.Smooth.Admissibility.EquivalenceStatement
Representation.Smooth.Contragredient.CompactDualityProof
Representation.Smooth.Contragredient.CompactDualityStatement
Representation.Smooth.Contragredient.Definitions
Representation.Smooth.Contragredient.FixedVectorsDefinitions
Representation.Smooth.Contragredient.LawsProof
Representation.Smooth.Contragredient.LawsStatement
Representation.Smooth.Definitions
Representation.Smooth.FixedVectors.Definitions
Representation.Smooth.SmallRealizationProof
Representation.Smooth.SmallRealizationStatement
Representation.Smooth.SmoothPart.BasicProof
Representation.Smooth.SmoothPart.BasicStatement
Representation.Smooth.SmoothPart.Definitions
Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Representation.Smooth.Transfer.PullbackProof
Representation.Smooth.Transfer.PullbackStatement
Representation.Smooth.Transfer.SubquotientProof
Representation.Smooth.Transfer.SubquotientStatement
Representation.Tensor.Finite
Representation.Tensor.FiniteEquivalences
Representation.Tensor.OneFactor
Representation.Twist.AdmissibilityProof
Representation.Twist.AdmissibilityStatement
Representation.Twist.AlgebraProof
Representation.Twist.AlgebraStatement
Representation.Twist.ContinuousCharacterProof
Representation.Twist.ContinuousCharacterStatement
Representation.Twist.Definitions
Representation.Twist.RealPower
Representation.Twist.SmoothProof
Representation.Twist.SmoothStatement
Representation.Twist.SubquotientDefinitions
Representation.Twist.SubquotientProof
Representation.Twist.SubquotientStatement
Representation.Unitary.Basic
Representation.Whittaker.Algebraic
Representation.Whittaker.GeneralLinear
Representation.Whittaker.Iwasawa
Topology.CompactNormCharacter
Topology.CompactOpen.ConjugationStabilizer
Topology.CompactOpen.NeighborhoodBasis
Topology.CompactOpen.NeighborhoodBasisStatement
Topology.Nonarchimedean.Subgroup
```

Directly encountered external imports:

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Fourier.FourierTransform
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Abelian.Subcategory
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Basic
Mathlib.Data.Finset.NatAntidiagonal
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.OpenMapping
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Baire.LocallyCompactRegular
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Compactness.SigmaCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Order.Compact
Mathlib.Topology.UrysohnsLemma
```
