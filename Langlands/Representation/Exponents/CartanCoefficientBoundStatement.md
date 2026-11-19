# Polynomial Cartan coefficient bound from weak normalized Jacquet exponent bounds

Author: Worker 960.

`Langlands.GLCartanCoefficientBoundStatement` is a `Prop`-valued definition
that states an estimate. This pair does not prove the estimate. It also does
not prove temperedness or any integrability statement. The proposition is a
**derived specialization** of the implication (ii) ⇒ (i) of Waldspurger [W03],
Proposition III.2.2, pp.265–266, to the actual normalized Cartan chamber of
`GL_n`. That implication rests on Lemma II.1.1, p.251, Proposition I.4.3,
p.245, and the finite chamber-strata argument in the proof of Corollary III.1.2,
pp.263–264. The exact coordinate weight and the uniform pointwise estimate
below do not appear verbatim in the source (see "Original sources" below).

## Exact statement and scope

The proposition quantifies over every prime `p`, every finite p-adic field
`F : PadicField.{uF} p`, every supplied compatible `T : F.TopologicalData`, and
every positive rank `n`. Independently, it quantifies over a carrier
`V : Type uV` with `AddCommGroup V` and `Module ℂ V`, a representation `ρ` of
the actual group `GeneralLinear n F.Carrier` on `V`, and a homomorphism
`ω : F.Carrierˣ →* ℂˣ`. The field universe `uF` and the carrier universe `uV`
are independent level parameters. Smoothness and admissibility use the
topology supplied by `T`, which the `letI` in the proposition installs.

The hypotheses are exactly:

1. `IsAdmissible ρ`, which includes smoothness.
2. For every `a : F.Carrierˣ` and every `v : V`,
   `ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v`.
3. For every standard ordered block shape `B : GeneralLinear.BlockShape n`,
   every character `χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` satisfying
   `T.IsJacquetExponent B ρ χ`, and every block scalar
   `a : Fin B.length → F.Carrierˣ`, if
   `i ↦ T.normalizedAbs (a i : F.Carrier)` is `Monotone`, then
   `‖(χ a : ℂ)‖ ≤ 1`.

Hypotheses 1 and 2 match the corresponding premises of
`GLTemperedExponentCriterionStatement`. Hypothesis 3 is word for word the
right-hand side of that criterion's equivalence. The criterion is only a
specification comparison: its module is not imported and nothing from it is
used. Here `T.IsJacquetExponent B ρ χ` is the published notion: `χ` has open
kernel, and `χ` is a generalized eigencharacter of the **normalized** upper
Jacquet module along `B`, restricted to the split centre of the block Levi.

The proposition has no unitarity premise for `ω`, and none is needed. Assume
`V ≠ 0`, and take the one-block shape (length `1`, one block of size `n`). Its
unipotent radical is trivial and its modulus is trivial. The split centre then
acts on the Jacquet module through `a ↦ ω (a 0)`. Smoothness at a nonzero
vector makes the kernel of this character open, so the character is a Jacquet
exponent. Every one-entry tuple is monotone, so hypothesis 3 gives
`‖ω a‖ ≤ 1` for every `a`. Applying this to `a⁻¹` gives `‖ω a‖ = 1`. This
derivation is explanatory only; it is not proved here. The one-block and
central test is kept in hypothesis 3 exactly as in the criterion. For the zero
carrier, `ω` is unconstrained. The conclusion still holds there because every
coefficient vanishes and the right-hand side is nonnegative.

The proposition does not assume irreducibility, finite length, unitarity,
a nonzero carrier, a finite-dimensional carrier, or a globally finite
exponent spectrum. It assumes no `Ξ` estimate, no coefficient bound, no
spectral decomposition, and no envelope function.

For each `v : V` and `ℓ : SmoothDual ρ`, the conclusion gives a real `C` and
`d : ℕ` with `0 < C`. They are uniform in every integer tuple
`lam : Fin n → ℤ` with `GeneralLinear.CartanQuotient.Normalized lam` and in
both `k₁, k₂ ∈ GeneralLinear.CartanQuotient.maximalCompact T n`:

```text
‖ℓ.1 (ρ (k₁ * representative T lam * k₂) v)‖
  ≤ C * Real.sqrt (delta T lam) * (height lam)^d.
```

All named functions are the existing `GeneralLinear.CartanQuotient`
definitions from `Langlands.Group.GL.CartanQuotientDefinitions`:

- `maximalCompact T n` is the actual image of `GL_n(O_F)` in `GL_n(F)`.
- `representative T lam` is the actual diagonal matrix
  `Iwasawa.torus (uniformizerUnit T) lam`, whose entries are `ϖ^(lam i)` for
  the specified uniformizer.
- `Normalized lam` means `Antitone lam`, all `lam i ≥ 0`, and some
  `lam i = 0`.
- With `q = T.residueCardinality`:

```text
degree lam = ∑_{i<j} (lam i - lam j),
delta T lam = q^(-degree lam)          (integer power),
height lam = 1 + ∑_i |lam i|.
```

The constants may depend on `p, F, T, n, ρ, ω, v, ℓ`. The proposition makes no
uniformity claim in these inputs. The factor is the positive half modulus
`sqrt(delta) ≤ 1`, not its inverse. `d = 0` is allowed. At rank one,
normalization forces `lam = 0`, so `delta = 1` and `height = 1`, and the
conclusion says only that the coefficient is bounded on `K × K`.

This is a pointwise polynomial coefficient estimate on a chamber of
representatives. It is **not** a redefinition of temperedness. The Library's
`T.IsTempered` is `L^(2+ε)` integrability modulo the centre with a unitary
central character. It is also not the final integrability theorem. To pass
from this estimate to temperedness one also needs the Cartan disjointness and
volume estimates of [W03] I.1 (4)–(5), pp.240–242, and a lattice summation.
None of these is asserted here.

## Relation to existing Library results

- `GLStrictCartanCoefficientBoundStatement`
  (`Langlands.Representation.Exponents.StrictCartanCoefficientBoundStatement`)
  is the strict analogue. It assumes `‖χ a‖ < 1` whenever two absolute values
  differ, and it assumes `‖ω a‖ = 1`. It concludes an extra decay factor
  `r^(height - 1)` with `r < 1`. This weak statement differs from it in three
  ways: its hypothesis is the criterion's weak test with no unequal-values
  premise, it has no unitarity premise, and its conclusion has no decay
  factor.
- `GLProductLeviChamberCoefficientBoundStatement`
  (`Langlands.Representation.Classification.ProductLeviChamberBoundStatement`)
  is a blockwise bound for admissible representations of a block Levi. For
  each `η > 0` it bounds coefficients at block-diagonal chamber elements by
  `c ∏_j delta(lam_j)^(1/2 - η)`. On the Cartan chamber of `GL_n`, the
  polynomial factor `height^d` here is sharper than any such loss.
- `GLTemperedExponentCriterionStatement` is already proved in the Library as
  `Langlands.glTemperedExponentCriterion`
  (`Langlands.Representation.Classification.TemperedExponentProof`). That proof
  goes through product-Levi results, not through this proposition. The present
  statement is therefore an independent, sharper estimate and is not an input
  to the published criterion proof.

## Original sources and reading

[W03] J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003),
235–333, DOI `10.1017/S1474748003000082`.
Literature ID `waldspurger-2003-plancherel`; SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Retained original:
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
PDF page = printed page − 234. Pages read: pp.239–245, 251, 263–266.

- **I.1 (4)–(5), pp.240–242.** These give the disjoint decomposition
  `G = ⋃ K m K` over `m ∈ M̄0+ / M0¹` and the volume bounds
  `C1 δ0(m)^(-1) ≤ mes(KmK) ≤ C2 δ0(m)^(-1)`. They explain why
  `sqrt(delta)` times a polynomial is the natural tempered size on the
  chamber. They are not part of this proposition.
- **I.2–I.3, pp.242–243.** An `A_M`-finite function is a finite sum of
  characters times polynomials. An admissible `V` is the direct sum of its
  generalized `A_G`-eigenspaces `V_χ`, `χ ∈ Exp(π)`. Nothing there makes
  `Exp(π)` finite for an arbitrary admissible `π`. The normalized Jacquet
  action is `π_P(m) j_P(v) = δ_P(m)^(-1/2) j_P(π(m) v)`.
- **Theorem I.4.1 and Proposition I.4.3, p.245.** I.4.1 is Casselman's
  canonical pairing. I.4.3: for a fixed pair `(v, v̌)` there is `t > 0` such
  that for every `m ∈ M̄0+`,
  `δ_P(m)^(-1/2) ⟨π(m)v, v̌⟩ = ⟨π_P(m) j_P(v), ǰ_P̄(v̌)⟩_P`
  with `P = P_{m,t}`. Here `P_{m,t}` is the standard parabolic whose Levi
  simple roots are those `α` with `⟨α, H0(m)⟩ ≤ t`. These chamber strata are
  finite in number.
- **Lemma II.1.1, p.251.** This is the comparison
  `C1 δ0(m)^(1/2) ≤ Ξ(m) ≤ C2 δ0(m)^(1/2) (1 + σ(m))^d`. Its proof fixes a
  stratum `M̄0+(P)`, covers it by `A_M C` with `C` compact, fixes `h ∈ C`, and
  uses a polynomial `Q` on `a_M`.
- **Corollary III.1.2, proof, pp.263–264.** The proof restricts to
  `M̄0+ ∩ G¹` by I.1 (4) and a K-finiteness argument. As in II.1.1 it fixes a
  standard `P` and vectors `v_P`, `v̌_P̄`. It writes
  `a ↦ δ_P(a)^(1/2) ⟨π_P(a) v_P, v̌_P̄⟩_P` as
  `δ_P(a)^(1/2) ∑_{χ∈E} χ(a) Q_χ(H_M(a))`, with `E` a **finite** subset of
  `Exp(π_P)` and each `Q_χ` a polynomial.
- **Proposition III.2.2, pp.265–266.** Temperedness is defined on p.265
  (III.2): every coefficient is bounded by `c Ξ(g) (1 + σ(g))^r`. For
  (ii) ⇒ (i), p.266 says that the argument of III.1.2 applies, and that the
  "seule modification" is that one has only `|χ(a)| ≤ 1` for
  `a ∈ Ā0+ ∩ A_M`. The (iii) ⇒ (ii) step and the converse are not used.

Errata: the "Notation and source corrections" section of the Library note
`notes/plancherel/waldspurger-source-map.md` lists corrections on pp.270,
301, 305, 325 and 330. None concerns the pages cited here. The p.270
correction (III.5.1) is relevant by analogy only. There the polynomials
`Q_χ` may depend on the `a_G`-component when `A_G` does not act by a
character. Here `A_G` does act by a character, which is the point of the
central-growth discussion below. This records the search scope; it is not a
claim that no other correction exists.

## How the GL formula is derived, and what remains to be proved

The source's conclusion uses `Ξ`, `σ`, `G¹` and arbitrary `g ∈ G`. This
proposition fixes the concrete normalized integer chamber with its exact
`height` and `delta`, and the two actual compact factors. The following steps
explain the derivation. None of them is proved by this definition.

1. **Finitely many K-translates.** The integral subgroup
   `K = maximalCompact T n` is compact in the supplied topology. The
   stabilizer of the smooth vector `v` is open, so its intersection with `K`
   has finite index in `K`. Hence the set `{ρ(k) v : k ∈ K}` is **finite**,
   not merely finite-dimensional. The same holds for the smooth functional
   `ℓ` under the dual action, since
   `ℓ(ρ(k₁ a k₂) v) = (ρ^∨(k₁⁻¹) ℓ)(ρ(a)(ρ(k₂) v))`.
   So `k₁, k₂` range over finitely many pairs of vectors. A maximum of the
   finitely many resulting constants and degrees gives the uniformity in
   `k₁, k₂`. This uses only smoothness and compactness; no
   finite-dimensional carrier is involved.
2. **Strata.** For the upper Borel subgroup, `|ϖ^(lam i)| = q^(-lam i)`. So a
   decreasing `lam` gives increasing absolute values, which is the monotone
   chamber of hypothesis 3. Take a common threshold `t` as in I.4.3 for the
   finitely many translated pairs. Then the gaps `s_i = lam i - lam (i+1)` are
   each declared small or large. Small gaps join adjacent coordinates into
   blocks, which gives a standard block shape `B`. The within-block offsets
   are bounded, so there are finitely many of them. The remaining part is a
   block-scalar lattice point. This mirrors the strata `M̄0+(P) ⊂ A_M C` of
   II.1.1.
3. **Coefficient-relevant finite spectra.** For each of the finitely many
   shapes, pairs and offsets, the Jacquet image of the translated vector lies
   in a finite-dimensional space fixed by a compact open subgroup of the Levi.
   Jacquet admissibility is needed for this. The split centre preserves that
   space, so the orbit span is finite-dimensional. Its generalized-character
   decomposition gives the finite set `E` of III.1.2. Each character must be
   identified with an actual `T.IsJacquetExponent B ρ χ`: open kernel,
   generalized eigencharacter of `T.splitCentreJacquet`, and a uniform
   nilpotence power. The pairing then gives finite sums of
   `χ(a) Q_χ(valuations)`. Only these finite sets are used. Admissibility of
   an arbitrary `ρ` does **not** make the global exponent set finite, and no
   such claim is made.
4. **Weak test and polynomial growth.** On the block-scalar part, each
   relevant `χ` satisfies `‖χ(a)‖ ≤ 1`. This is because the block scalars of a
   normalized `lam` have monotone normalized absolute values, which is exactly
   the "seule modification" of p.266. With no strict decay, the polynomials
   `Q_χ` remain. Their degrees are bounded by the finite nilpotence powers,
   which gives `|Q_χ| ≤ C' (height lam)^d`. Shifting from block-scalar
   valuations to `lam` changes the height by a bounded amount, which is
   absorbed into `C`.
5. **Modulus.** The normalized Jacquet action contributes `δ_(P_B)^(1/2)`. On
   block scalars this equals the upper-Borel half modulus, since roots inside
   a block contribute nothing. On a bounded offset the remaining ratios are
   finitely many positive constants. Identifying the product with
   `Real.sqrt (CartanQuotient.delta T lam)` is a required GL calculation.
6. **Central growth.** Subtracting the last coordinate selects, in each class
   of antitone integer tuples modulo common integer shifts, exactly one
   normalized tuple: antitone, nonnegative, with last coordinate `0`
   (`GeneralLinear.CartanQuotient.normalized_iff_antitone_last_eq_zero` in
   `Langlands.Group.GL.CartanQuotientLawsProof`). These normalized tuples
   index the double cosets of the image of `K` in `GL_n(F)/Z`: every point of
   the central quotient lies in exactly one cell `cell T lam`
   (`GeneralLinear.CartanQuotient.cartanQuotientCover` and
   `GeneralLinear.CartanQuotient.cartanQuotientDisjoint` in
   `Langlands.Group.GL.CartanQuotientCoverProof`). They do **not** give a
   diagonal representative of each individual class in `GL_n(F)/Z`. For
   example, the class of the matrix `[[1, 1], [0, 1]]` in `GL_2(F)/Z`
   contains no diagonal matrix, although it lies in the cell of the zero
   tuple. Replacing `lam` by `lam + c` multiplies `a(lam)` by the central
   scalar `ϖ^c`. The scalar matrices act on all of `V` by
   the scalar `ω`, hence also on every Jacquet image, and the modulus of a
   scalar is `1`. So the `a_G` direction contributes only the factor
   `ω(·)`, which has norm `1` when `V ≠ 0` (see above), and **no**
   polynomial. This is the case where the p.270 correction is harmless. In
   [W03] the bound `c Ξ(g) (1 + σ(g))^r` over all of `G` still allows
   polynomial growth along `A_G` for representations with nilpotent central
   action. The scalar premise excludes that here.
7. **Degenerate cases.** For a zero coefficient, including the zero carrier,
   take `C = 1` and `d = 0`. The bound holds because `sqrt(delta) ≥ 0` and
   `height ≥ 1`. The one-block stratum needs no noncentral test; at rank one
   it is the whole chamber.

### A direct route and its precise missing proofs

The published strict proof `Langlands.glStrictCartanCoefficientBound`
(`Langlands.Representation.Exponents.StrictCartanCoefficientBoundProof`)
avoids strata and pairings. It compresses the coefficient to the
finite-dimensional space `V^K` of vectors fixed by one small compact open
subgroup. There the Cartan representatives act multiplicatively as products
of `n - 1` compressed fundamental coweights `diag(ϖ I_k, I_(n-k))`. Let `a`
be a contracting two-block scalar and `δ_P(a)` the positive Levi modulus
`T.leviModulus B (B.blockScalarLevi F.Carrier a)`. For each nonzero
eigenvalue `μ` of the compression by `a`, the strict proof constructs an
actual two-block exponent `χ` with `T.IsJacquetExponent B ρ χ` and
`χ(a) = μ / sqrt(δ_P(a))`, that is, `μ = sqrt(δ_P(a)) χ(a)`
(`StrictCartanCoefficientBoundProof.lean`, the construction of `c` and the
identity `hχa` in `StrictCartanBound.norm_eigenvalue_lt_sqrt_leviModulus`).
The inverse half modulus here is the normalization of the Jacquet action. The
same route would prove this proposition once three ingredients are supplied:

1. A weak analogue of `StrictCartanBound.norm_eigenvalue_lt_sqrt_leviModulus`:
   every eigenvalue `μ` of the compression by a contracting two-block scalar
   `a` satisfies `‖μ‖ ≤ sqrt(δ_P(a))`. For `μ ≠ 0`, hypothesis 3 applied to
   the exponent `χ` above gives `‖χ(a)‖ ≤ 1`, hence
   `‖μ‖ = sqrt(δ_P(a)) ‖χ(a)‖ ≤ sqrt(δ_P(a))`. For `μ = 0` the bound holds
   because `sqrt(δ_P(a)) > 0`.
2. A polynomial power bound. Let `s > 0`, let `W` be a complex space of
   finite dimension `N`, and let `A` be an endomorphism of `W` all of whose
   eigenvalues have norm at most `s`. Then there is a constant `C`, depending
   on `A` and `s`, with `endNorm (A^j) ≤ C (1 + j)^(N-1) s^j` for every
   `j ∈ ℕ`. In the application `s = sqrt(δ_P(a))` is positive. The
   hypothesis `s > 0` is needed: for the nonzero nilpotent matrix
   `[[0, 1], [0, 0]]`, `s = 0` and `j = 1` the right side is `0`. The Library's
   `EndomorphismBound.exists_endNorm_pow_le` and
   `EndomorphismBound.matrix_pow_bound` (`Langlands.Analysis.EndomorphismPowerBound`)
   only give `C r^j` for `r` strictly larger than the spectral bound. That
   exponential loss would not give a polynomial factor.
3. The assembly. The product of the `n - 1` power bounds is
   `C ∏_k (1 + s_k)^(N-1) · sqrt(delta T lam)`, and one needs
   `∏_k (1 + s_k)^(N-1) ≤ height(lam)^((n-1)(N-1))`. Also needed is the
   finite K-translate reduction of step 1 above, which the strict proof
   already implements.

`HarishChandraSchwartz.exists_exponentialPolynomial_of_finiteDimensional`
(`Langlands.HarmonicAnalysis.HarishChandraSchwartz.FiniteFunctionExpansion`)
supplies the I.2 expansion of a function with finite-dimensional translation
span. It could serve the literature route of step 3.

## Dependencies and independence

The direct Lean imports are only
`Langlands.Group.GL.CartanQuotientDefinitions`,
`Langlands.Representation.Exponents.Jacquet`, and
`Langlands.Representation.Smooth.Contragredient.Definitions`. They supply the
actual group, the compact subgroup, the representatives and weights, the
Jacquet exponents, and the smooth dual. No imported pair is changed. No
statement is assumed as a hypothesis or field, and no envelope replaces the
explicit formula. Published statements, pending tasks, and literature
citations are not treated as proofs.

A proof must not go through regular Langlands uniqueness, square-integrable
classification, or anything depending on them. This pair states only the
target; an exact-target proof task is to be published separately after this
statement is in the Library.
