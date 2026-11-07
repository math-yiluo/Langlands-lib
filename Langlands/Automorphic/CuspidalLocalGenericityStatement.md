# Actual local genericity of all cuspidal presentations

Author: Worker 1809.

`Langlands.Automorphic.CuspidalLocalGenericityStatement.{uF, uQ}` is a
proposition definition. It is the published
[`CuspidalUnitaryLocalGenericityStatement`](CuspidalUnitaryLocalGenericityStatement.md)
with exactly one premise removed: the hypothesis
`Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`.
It therefore covers every actual cuspidal realization and presentation that
[`AssociatedGammaStatement`](AssociatedFactorStatement.md) quantifies over,
because that consumer imposes no central-character condition. This module
proves no genericity, constructs no Whittaker functional, and constructs no
norm or determinant twist.

The module also proves one implication,
`CuspidalLocalGenericityStatement.toUnitary`: the new proposition implies
`CuspidalUnitaryLocalGenericityStatement.{uF, uQ}`. The proof applies the
hypothesis to the same arguments and ignores the unitary premise. This
machine-checks that the new statement only removes that premise. It does not
change, prove, or duplicate the unitary target.

## Exact quantifiers and original action

The statement quantifies over every `F : Type uF` with `Field F`,
`NumberField F`, and `CompactSpace (Langlands.Global.AdeleQuotient F)`, every
`r : ℕ`, every
`T : Langlands.Automorphic.CuspidalOperatorRealization F r`, every
`P : Langlands.Automorphic.CuspidalSpectralPresentation.{uF, uQ} T`, every
finite place `v`, and every pair of proofs
`hI : (P.localComponent v).IsIrreducible` and
`hA : (P.localComponent v).IsAdmissible`. The compactness instance is the
one in the existing cuspidal interface. The rank is `r + 1`, so it is always
positive. No condition on the central character of `T` appears, and no
unitarizing twist is chosen. Write
`K = Langlands.Global.CompletionPadic.padicField v` and

```text
ρ = ((P.localComponent v).padicObject hI hA).obj.representation.
```

The statement installs `K.canonicalTopologicalData.topology` and
`K.canonicalGeneralLinearTopology (r + 1)`. For every
`ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier`, the
conclusion is exactly `Langlands.Whittaker.IsGeneric ψ r ρ`. The character
type already requires continuity, nontriviality, and values in the unit
circle. There is no further choice of topology or character class.

The [`padicObject` interface](PadicLocalCategory.md) keeps the original
embedded form-space carrier. It also keeps the original action of the actual
matrix group `GL_(r+1)(K.Carrier)`, with canonical smoothness, irreducibility,
and admissibility. It does not choose an equivalent Whittaker model. The
original local carrier lies in `uF`. The carriers of `P.localFactor` may lie in
the independent universe `uQ`, and the two universes are not set equal.
Quantifying over supplied presentations does not assert that they exist.
The statement takes no Whittaker functional, weak association, arithmetic
realization, central character, or twist as an input.

## Meaning of genericity

The shared [`Whittaker.IsGeneric`](../Representation/Whittaker/GeneralLinear.md)
is a conjunction of three conditions: irreducibility, admissibility for the
selected group topology, and the existence of an actual nonzero complex linear
functional `ℓ` on the carrier of `ρ` satisfying

```text
ℓ(ρ(u) x) = ψ.complex(∑ i : Fin r, u[i, i+1]) * ℓ(x)
```

for every standard upper-unipotent matrix `u` and every vector `x`. The
matrix indices are precisely `i.castSucc` and `i.succ` in `Fin (r + 1)`, and
the sign is positive. Rank one is included: when `r = 0`, the upper-unipotent
group is trivial and the sum is empty. Neither a functional nor genericity is
an input. No multiplicity-one result is asserted.

## Provenance: an internal derived extension

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), Théorème 2.4 (printed p.445) and
Appendix A.2 (printed p.453), uses genericity only for cuspidal
representations with unitary central character. That is the source of the
unitary target (`henniart-2000-simple-proof`). The present proposition drops
that restriction. It is therefore not a literal translation of Henniart. It
is an internally derived formulation that serves `AssociatedGammaStatement`
(Henniart's Théorème 2.3, which has no unitary hypothesis).

The unrestricted assertion is itself standard. Cogdell's Fields lectures
(`cogdell-2003-fields-lectures-www`, SHA-256
`2c5ec050a6db216dcd2104b7fe266ddc03e4db7c7d300239e60d6ee9c40618a7`;
one-based PDF page = printed page + 4) state it without a central character:

- Lecture 2, Definition 2.3 (printed p.18): smooth automorphic forms, with no
  central-character condition. Only the L² forms in §4 of that lecture fix a
  unitary `ω`.
- Lecture 2, Definition 2.5 (p.19) and the remark on p.20: cusp forms are
  defined by vanishing constant terms along proper parabolics, and the
  standard maximal parabolics suffice.
- Lecture 4 §1 (pp.29–31): the Fourier expansion of `φ ∈ V_π ⊂ A^∞_0`, for an
  arbitrary smooth cuspidal representation. It begins with the last column
  of `N` and uses `(k\A)^ ≅ k` (p.30). §2 (p.31) states that `W_φ ≠ 0` for
  `φ ≠ 0`.
- Corollary 4.1.2 (p.33): a cuspidal `π ≅ ⊗' π_v` and each `π_v` are generic.
- Lecture 5 (p.37) imposes unitary central characters only afterwards, and
  calls that condition "not restrictive".

The relevant pages were read directly. The Library's cuspidality, `IsCuspidal`
in [`ConstantTerm`](ConstantTerm.md), is the maximal-parabolic version of that
definition. The actual forms of a `CuspidalOperatorRealization` are continuous
and invariant on the left under `GL_n(F)`.

## Source audit and limitations

- **Getz–Hahn 2024** (`getz-hahn-2024-automorphic-representations`),
  Theorem 11.3.6 (printed p.298, one-based PDF p.309), is the Whittaker
  expansion for `φ ∈ L²_cusp([GL_n])` with `[G] = A_G G(F)\G(A)`. Such `φ` are
  invariant under `A_G`, so their central character is unitary and trivial on
  `A_G`. The theorem therefore does not literally cover nonunitary central
  characters. It is proved there only for `n = 2` (pp.298–299), citing
  [Cog07, §1.1] for general `n`. Its global coefficient (11.6), printed p.297,
  takes values in the space (11.7) of functions with `W(ng) = ψ(n) W(g)`. This
  is the same left equivariance as Cogdell's `W_φ`. Passing from a global to a
  local Whittaker functional is left to Exercise 11.3. The book is used here
  only as a cross-check of these conventions.
- **Getz–Hahn errata** (`getz-hahn-2024-errata-2026-10`, SHA-256
  `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`), all five
  pages read. The only Chapter 11 entry is for §11.5: the character `ψ` is
  defined twice at the top of p.304. No entry concerns §11.3.
- **Cogdell 2003**: the unitary twist remark (Lecture 3 §4, p.26) is stated
  without proof. It says that every cuspidal representation is an unramified
  twist `π ⊗ χ(det)` of a unitary one "due to the rapid decrease of cusp
  forms". Route B below relies on this remark, so its proof is an obligation.
  The Fourier expansion on pp.30–31 is sketched ("not hard to prove"). Route A
  replaces its convergence by the uniqueness argument below.
- **Weil, Basic Number Theory** (`weil-1973-basic-number-theory`, SHA-256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`;
  one-based PDF page = printed page + 17). Chapter IV §2, Theorem 3 (printed
  p.66): for a nontrivial character `χ` of `k_A` that is trivial on `k`,
  `e' ↦ (e ↦ χ([e, e']))` is an isomorphism of `E'_A` onto the dual of `E_A`.
  The characters trivial on `E` are exactly those coming from `E'`. The proof
  on p.69 constructs such a `χ` for every A-field. Corollary 1 (p.69): every
  local component `χ_v` is nontrivial.
- **Character transport.** The convention is from Jacquet, Piatetski-Shapiro
  and Shalika, *Rankin–Selberg Convolutions* (1983), printed p.377 and §2.1
  p.385 (`jpss-1983-rankin-selberg`). Additive characters are parameterized as
  in Bernstein–Zelevinsky (1976), §5.3 p.44
  (`bernstein-zelevinsky-1976-representations-gln`). Both sources are as
  recorded in the unitary target's Markdown. If `ℓ` is equivariant for
  `ψ_a(x) = ψ(a x)`, then `x ↦ ℓ(ρ(d) x)` is equivariant for the rescaled
  character, where `d = diag(a^r, …, a, 1)`, on the same original
  representation.

## Route A (recommended): direct Fourier–Whittaker route

This route needs no central character, no twist, and no unitarity. Let
`n = r + 1`, and let `N` be the upper-unipotent group.

1. **Global character.** Fix a nontrivial continuous unitary character `ψ_A`
   of `Langlands.Global.Adeles F` that is trivial on the diagonal copy of `F`
   (Weil, p.69). Its finite restriction is
   `Langlands.Global.HeckeFunctionalEquation.finiteAdditiveRestriction ψ_A v :
   AddChar (FiniteCompletion F v) Circle`. It is continuous by
   `continuous_finiteAdditiveRestriction`, and nontrivial by Weil's
   Corollary 1. The Library does not yet prove either the existence of `ψ_A` or
   this nontriviality.
2. **Whittaker coefficient on actual forms.** For each actual form `f` in the
   realization, define
   `W_f(g) = ∫_{N(F)\N(A)} f(n g) ψ_A^{-1}(∑ n_{i,i+1}) dn`. The integral uses a
   right-`N(A)`-invariant probability measure on the compact quotient, for
   example the product of the Library's `adeleQuotientHaar` over the matrix
   coordinates. Construction obligations: this measure; its invariance;
   Fubini decompositions along normal unipotent subgroups; and continuity of
   `g ↦ W_f(g)`.
3. **Nonvanishing (`f ≠ 0` implies `W_f ≢ 0`).** For `2 ≤ k ≤ n + 1`, let
   `U_k ⊂ N` be the matrices supported in columns `≥ k` (so `U_{n+1} = 1` and
   `U_2 = N`). Let `ψ_k(u) = ψ_A(∑_{j ≥ k} u_{j-1,j})`, and set
   `f_k(g) = ∫_{U_{k+1}(F)\U_{k+1}(A)} f(u g) ψ_{k+1}^{-1}(u) du`. Then `f_n = f`,
   `f_1 = W_f`, and `f_{k-1}` is the `e_{k-1}` Fourier coefficient of
   `c ↦ f_k(c g)` on the column group `C_k(F)\C_k(A) ≅ (A/F)^{k-1}`. Each `f_k`
   is left invariant under `U_k(F)` and under `δ = diag(γ, 1)` for
   `γ ∈ GL_{k-1}(F)`: `δ` normalizes `U_{k+1}` and preserves `ψ_{k+1}`, and `f`
   is automorphic. Every continuous automorphism of a compact group preserves
   its normalized Haar measure.

   By Weil's Theorem 3, the characters of `(A/F)^{k-1}` are `x ↦ ψ_A(ξ·x)` for
   `ξ ∈ F^{k-1}`. The `ξ = 0` coefficient vanishes. Indeed, the unipotent
   radical of the standard `(k-1, n-k+1)` block parabolic is normal in `U_k`,
   and the remaining character is trivial on it. The inner integral is
   therefore the Library's `constantTerm` with `a = k - 1` and `b = n - k + 1`,
   which `IsCuspidal` makes zero. For `ξ ≠ 0`, choose `γ` with `ξ = e_{k-1} γ`.
   The coefficient at `ξ` is then `f_{k-1}(δ g)`. Hence `f_{k-1} ≡ 0` makes
   every Fourier coefficient of `c ↦ f_k(c g)` vanish. Uniqueness of Fourier
   coefficients of continuous functions on compact abelian groups gives
   `f_k ≡ 0`. Descending induction from `f_1 = W_f ≡ 0` reaches `f = 0`. This is
   Cogdell's argument (pp.30–31) with the convergent expansion replaced by
   uniqueness. Real obligations: the duality, the uniqueness theorem, the
   transitivity of `GL_{k-1}(F)` on nonzero row vectors, and the measure
   identities above.
4. **Local functional on the original component.** The component
   `P.localComponent v` is nonzero
   (`CuspidalSpectralPresentation.localComponent_ne_bot`). Its vectors are
   actual cuspidal forms (`localComponent_isCuspidal`), and its action is
   right translation through the local inclusion. Choose a nonzero `f` in it
   and `g` with `W_f(g) ≠ 0`. Write `g = g^{(v)} · ι_v(g_v)`, where `g^{(v)}` has
   trivial `v` component. Then `ℓ(x) = W_x(g^{(v)})` is a linear functional on
   the original carrier and `ℓ(ρ(g_v) f) ≠ 0`. Since `g^{(v)}` commutes with
   `ι_v(GL_n(F_v))` and the measure is right `N(A)` invariant,
   `ℓ(ρ(u) x) = finiteAdditiveRestriction ψ_A v (∑ u_{i,i+1}) · ℓ(x)`.
5. **Arbitrary local character.** By continuity, the restriction is trivial on
   `ϖ^m 𝒪_v` for some `m`. Replace `ℓ` by `x ↦ ℓ(ρ(d) x)` with
   `d = diag(ϖ^{m r}, …, ϖ^m, 1)`, the conjugation implemented by
   [`Whittaker.CharacterChange`](../Representation/Whittaker/CharacterChange.md).
   The character becomes `x ↦ ψ_v(ϖ^m x)`, which is trivial on integers and
   nontrivial. Then
   `LocalRealization.isGeneric_of_integerTrivial_character`
   ([`LocalWhittakerCharacterBridge`](LocalWhittakerCharacterBridge.md)), applied
   with the given `hI` and `hA`, yields `Whittaker.IsGeneric ψ r ρ` for every
   `ψ`. Internally it uses `isGeneric_iff_character` from
   [`Whittaker.PadicCharacterIndependence`](../Representation/Whittaker/PadicCharacterIndependence.md),
   which is built on
   [`PadicAdditiveCharacterSelfDuality`](../HarmonicAnalysis/PadicAdditiveCharacterSelfDuality.md).
   Irreducibility and admissibility are the supplied `hI` and `hA`.

## Route B (alternative): unitarizing twist plus the unitary target

This route needs the following separate construction and proof obligations.
None of them is supplied here, and unitarization is not tautological.

1. **Central character.** Prove that `T.HasCentralCharacter χ` holds for some
   continuous idele-class character `χ`. Route B needs this as a theorem: for
   example, Schur's lemma for the full operator algebra together with the
   archimedean and finite parts of the centre.
2. **Real exponent.** Find `σ ∈ ℝ` with `|χ| = |·|_A^σ`. The character `|χ|` is
   positive and trivial on the compact norm-one idele classes.
3. **Non-finite-order twist.** Construct the twist of `T` and `P` by
   `|det|_A^{-σ/(r+1)}` on actual `OperatorRealization`,
   `CuspidalOperatorRealization` and `CuspidalSpectralPresentation` data. The
   existing `OperatorDeterminantTwist`, `CuspidalSpectralDeterminantTwist`,
   `AutomorphicCentralCharacterDeterminantMultiplier` and
   `OperatorDeterminantUnitary` handle only finite-order characters, and they
   state that the enveloping differential action is unchanged. A
   non-finite-order `|det|^s` shifts that action by a scalar on the Lie algebra
   at the archimedean places. The new twist must therefore be constructed,
   together with its compatibility with cuspidality, irreducibility and the
   presentations.
4. **Local transport.** Identify the twisted local component with
   `(P.localComponent v) ⊗ |det|_v^{-σ/(r+1)}`, along with `hI` and `hA`. Apply
   the unitary target once it is proved. This gives a functional `ℓ'` on the
   twisted component. Transport it back to the original `ρ` by
   `ℓ(x) = ℓ'(x · |det|_A^{-σ/(r+1)})`. The result is still `ψ`-equivariant
   because `|det u|_v = 1` for unipotent `u`.

Route A avoids all of steps 1–4. It is recommended for the later proof task.

## Scope

This module defines a target and proves only the `toUnitary` specialization.
It establishes no genericity, Fourier expansion, global character, norm twist
or central character. The companion local unitarity target
[`CuspidalUnitaryLocalUnitarityStatement`](CuspidalUnitaryLocalUnitarityStatement.md)
is unrelated and is not used. A nonunitary local component need not be
unitary, so no such companion is implied here.
