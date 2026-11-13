# Reduction of the cuspidal Satake bound to the existence of central characters

Module `Langlands.Global.Factors.CuspidalSatakeBoundReduction`.

## 1. Content

The module states and proves

```
def CuspidalSatakeBoundReductionStatement.{u, uQ} : Prop :=
  OperatorRealization.IrreducibleCentralCharacterStatement.{u} →
    CuspidalSatakeBoundStatement.{u, uQ}

theorem cuspidalSatakeBoundReduction : CuspidalSatakeBoundReductionStatement.{u, uQ}
```

(both in namespace `Langlands.Global`). The two statements it connects are both in the
Library:

* `Langlands.Automorphic.OperatorRealization.IrreducibleCentralCharacterStatement.{u}`
  (module `Langlands.Automorphic.IrreducibleCentralCharacterStatement`): every irreducible
  `S : OperatorRealization F n` over a number field `F` has a unique Hecke character `χ`
  with `S.HasCentralCharacter χ`. This module uses only the existence part.
* `Langlands.Global.CuspidalSatakeBoundStatement.{u, uQ}` (module
  `Langlands.Global.Factors.CuspidalPairCompletedEquationReduction`): for every number field
  `F` with compact adele quotient, every `T : CuspidalOperatorRealization F r` and every
  `P : CuspidalSpectralPresentation.{u, uQ} T` with `HasIrreducibleAdmissibleComponents P`,
  there is a real `C` with `HasSatakeBound P C`, i.e. `‖α‖ ≤ q_v ^ C` for every finite place
  `v ∉ P.exceptional` and every Satake parameter `α` in
  `P.spectralSystem.eigenvalues v hv`, where `q_v = residueCardinality v`.

The proof does not use the hypothesis `HasIrreducibleAdmissibleComponents P`: at places
outside `P.exceptional`, irreducibility and admissibility of the local components are part of
the presentation's unramified data (`P.unramified`).

This is a reduction: `IrreducibleCentralCharacterStatement` is an open Library statement
(Task 5209), and this module does not prove it. Together with
`cuspidalPairCompletedEquationReduction`, it reduces the Satake-bound premise of the
completed cuspidal-pair functional equation (Task 5721) to the existence of central
characters.

## 2. Provenance

The statement is internal: a reduction step needed by Task 5721, not a theorem quoted from a
single source. The mathematics is classical:

* Jacquet–Shalika, *On Euler products and the classification of automorphic forms I*,
  Amer. J. Math. 103 (1981) (Library source
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`),
  Corollary (2.5) and remark (3), printed p.515 (PDF p.17), prove the much stronger bound
  `|α| < q^(1/2)` for the Satake parameters of local components of unitary cuspidal
  representations (using genericity). Here only the weak form of
  `CuspidalSatakeBoundStatement` is needed: some exponent `C` for each presentation.
  The module proves it by the elementary "trivial bound" for unitary representations: a
  Hecke operator `1_{K g K}` acts on the spherical vector of a unitary representation as a sum
  of `[K g K : K]` unitary operators, so its eigenvalue has absolute value at most
  `[K g K : K]`. This argument is internal; it is not taken from the sources cited here.
* Getz–Hahn, *An Introduction to Automorphic Representations* (2024)
  (`getz-hahn-2024-automorphic-representations`), §11.7, printed p.309 (PDF p.320): because
  `L(s, π ⊗ |det|^(s_1) × π' ⊗ |det|^(s_2)) = L(s + s_1 + s_2, π × π')`, one may assume
  "without loss of generality" that the central characters are normalized (trivial on
  `A_GL_n`). The module uses the same device in the form of a twist by the Hecke character
  `‖ω‖ ^ (-1/n)`, which makes the central character `ω` unitary and multiplies the Satake
  parameters at `v` by a number of absolute value `q_v ^ (-β)`.

## 3. Proof

### 3.1 Local bound (namespace `Langlands.Unramified`)

Fix a p-adic field `F` with residue cardinality `q`, `m = r + 1`, and an automorphic object
`A` of `GL_m(F)` whose representation is unitarizable (`IsUnitarizable`, i.e. there is an
`InvariantPositiveForm b`) and has spherical Hecke spectrum `s`
(`HasSphericalHeckeSpectrum F A s`: a nonzero spherical vector `x`, and the `i`-th standard
Hecke operator acts on spherical vectors by `standardHeckeScalar F s i`).

1. `SatakeBound.norm_inner_apply_le`: Cauchy–Schwarz for `b` and invariance give
   `‖b(x, ρ(g) x)‖ ≤ Re b(x, x)`.
2. `SatakeBound.norm_le_card_of_smul_eq_sum`: if `c • x = ∑_{a ∈ ι} ρ(g_a) x` with `x ≠ 0`,
   then `‖c‖ ≤ #ι`. Pairing with `x` gives `‖c‖ Re b(x,x) ≤ ∑_a ‖b(x, ρ(g_a) x)‖ ≤ #ι Re b(x,x)`
   and `Re b(x, x) > 0` (`re_inner_self_pos`). The auxiliary lemmas `inner_smul_right` and
   `inner_sum_right` give linearity of `b` in the second variable.
3. `norm_standardHeckeScalar_le_card`: the Library identity
   `standardHecke_cornerAction_eq_sum` writes the `i`-th standard Hecke operator on a
   spherical vector as the sum over `CosetIndex k m i` (`k` the residue field) of the
   coset representatives `labelledRep`; by step 2,
   `‖standardHeckeScalar F s i‖ ≤ #CosetIndex k m i`.
4. `SatakeBound.card_cosetIndex_le`: `#CosetIndex Λ m i ≤ #Λ ^ (m * m + m)` when `#Λ ≥ 2`
   (at most `2 ^ m` subsets, and at most `#Λ ^ (m * m)` labellings of each).
5. `standardHeckeScalar F s i = q^(i(m-i)/2) · (-1)^i · coeff_i(P_s)`, where `P_s` is the
   Euler polynomial `∏_{α ∈ s} (1 - α X)`; since `q^(i(m-i)/2) ≥ 1`, every coefficient of
   `P_s` has norm at most `q ^ (m * m + m)` (coefficients of degree `> m` vanish).
6. `SatakeBound.norm_le_of_mem_of_coeff_le` (a Cauchy-type root bound): if every coefficient
   of `P_s` has norm at most `B`, then every `α ∈ s` has `‖α‖ ≤ max 1 (m B)`. Indeed
   `α⁻¹` is a root of `P_s`, `coeff_0 = 1`, and for `‖α‖ > 1` this gives
   `1 ≤ m B ‖α‖⁻¹`.
7. `norm_le_of_hasSphericalHeckeSpectrum`: combining, and using `m ≤ 2 ^ m ≤ q ^ m`
   (`two_le_residueCardinality`), every `α ∈ s` satisfies
   `‖α‖ ≤ q ^ (m * m + 2 * m)`.

### 3.2 Global part (namespace `Langlands.Global.CuspidalSatakeBound`)

Let `F` be a number field with compact adele quotient, `T : CuspidalOperatorRealization F r`,
`m = r + 1`.

1. `norm_le_of_hasUnitaryCentralCharacter`: if `T` has a unitary central character
   (`ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`), then for every
   presentation `Q` of `T`, every `v ∉ Q.exceptional` and every `α` in
   `Q.spectralSystem.eigenvalues v hv`, `‖α‖ ≤ q_v ^ (m * m + 2 * m)`. The local component
   at `v` is irreducible and admissible (from `Q.unramified`), hence unitarizable by the
   Library theorem `Automorphic.cuspidalUnitaryLocalUnitarity`, and it has spherical Hecke
   spectrum `Q.spectralSystem.eigenvalues v hv` (`Q.hasSpectrum`); apply §3.1.
2. `normRpow ω a`: the Hecke character `x ↦ ‖ω(x)‖ ^ a` (continuity from continuity of `ω`
   and of `t ↦ t ^ a` on `t > 0`). `norm_normRpow_pow_mul`: `(normRpow ω (-1/n)) ^ n * ω`
   has norm one at every idele class, for `n ≠ 0`.
3. `hasUnitaryCentralCharacter_heckeDeterminantTwist`: if `T.HasCentralCharacter ω`, then
   `T.heckeDeterminantTwist χ`, with `χ = normRpow ω (-1/m)`, has the unitary central
   character `χ ^ m * ω`. This uses the Library theorems
   `OperatorRealization.toFiniteRealization_heckeDeterminantTwist` and
   `FiniteRealization.heckeDeterminantTwist_hasCentralCharacter`.
4. `exists_norm_finiteUniformizerValue`: for a Hecke character `χ` there is `β` with
   `‖χ(ϖ_v)‖ = q_v ^ (-β)` at every finite place, where `χ(ϖ_v)` is
   `χ.finiteUniformizerValue v`. This is the Library theorem
   `HeckeEulerProduct.exists_norm_finiteComponent_uniformizer`, transported along
   `CompletionPadic.topologicalData_eq_canonicalTopologicalData` and
   `residueCardinality v = N(v)`.
5. `exists_hasSatakeBound`: if `T.HasCentralCharacter ω`, then every presentation `P` of `T`
   has a Satake bound. Put `χ = normRpow ω (-1/m)` and `Q = P.heckeDeterminantTwist χ`, a
   presentation of `T.heckeDeterminantTwist χ` with exceptional set
   `P.exceptional ∪ χ.finiteHeckeDeterminantTail m` and spectral system the system of `P`
   scaled by `χ(ϖ_v)` (Library `CuspidalSpectralPresentation.heckeDeterminantTwist`, whose
   spectral system is definitionally this scaling). Let `N = m * m + 2 * m` and
   `c_v = ∑_{α ∈ s_v(P)} |log_{q_v} ‖α‖|` for `v ∉ P.exceptional`. Take
   `C = max (N + β) (∑_{v ∈ Q.exceptional} c_v)`. For `v ∉ P.exceptional` and `α ∈ s_v(P)`:
   * if `v ∈ Q.exceptional` (one of the finitely many extra places), then
     `‖α‖ = q_v ^ (log_{q_v} ‖α‖) ≤ q_v ^ c_v ≤ q_v ^ C`;
   * otherwise `χ(ϖ_v) α` is a Satake parameter of `Q` at `v`, so by steps 1, 3 and 4
     `q_v ^ (-β) ‖α‖ ≤ q_v ^ N`, i.e. `‖α‖ ≤ q_v ^ (N + β) ≤ q_v ^ C`.
6. `cuspidalSatakeBoundReduction`: given `IrreducibleCentralCharacterStatement`, apply it to
   `T.realization` (irreducible by `T.irreducible`) with `n = m` to obtain a central
   character `ω`, and apply step 5.

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## 4. Remaining premise

`IrreducibleCentralCharacterStatement` (existence of a central character for irreducible
operator realizations, a form of Schur's lemma for the automorphic realization) remains
open; it is the subject of Task 5209. This module does not prove
`CuspidalSatakeBoundStatement` unconditionally.
