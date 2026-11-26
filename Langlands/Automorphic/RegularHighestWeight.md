# Regular highest weight at infinity

This module defines regular highest weight for the infinitesimal character of an
automorphic realization of `GL_n` over a number field. It strengthens Clozel's
regular algebraic type of `Langlands/Automorphic/RegularAlgebraic`.

## Definitions

- `Langlands.Global.ArchimedeanGL.IsRegularHighestWeightCharacter K n χ`: there is
  an integral weight `μ : EmbeddingIndex K → Fin n → ℤ` that is strictly decreasing
  (`StrictAnti`) at every embedding index, and `χ` is the infinitesimal character of
  highest weight `μ` (`IsHighestWeightCharacter`). The published
  `IsRegularAlgebraicCharacter` asks only that `μ` be nonincreasing (`Antitone`).
- `Langlands.Automorphic.OperatorRealization.HasRegularHighestWeight S`: the centre
  of the enveloping algebra acts on `S` through such a character.
- `OperatorRealization.IsoClass.HasRegularHighestWeight` for a full-operator class
  (some representative has it), and
  `CuspidalOperatorRealization.IsoClass.HasRegularHighestWeight c` for an irreducible
  cuspidal class (its full-operator class has it). These follow the pattern of the
  published `IsoClass.IsRegularAlgebraic`.

## Proved results

- `IsRegularHighestWeightCharacter.isRegularAlgebraicCharacter`: a strictly
  decreasing weight is nonincreasing, so the character is regular algebraic.
- `HasRegularHighestWeight.isRegularAlgebraic`,
  `OperatorRealization.IsoClass.HasRegularHighestWeight.isRegularAlgebraic` and
  `CuspidalOperatorRealization.IsoClass.HasRegularHighestWeight.isRegularAlgebraic`:
  the same implication for realizations and classes.
- `hasRegularHighestWeight_iff_of_equivalence` and
  `isoClass_hasRegularHighestWeight_iff`: the property is invariant under
  full-operator equivalence, so a class has it exactly when every representative
  has it. The proofs reuse the published
  `hasInfinitesimalCharacter_iff_of_equivalence`.

## Meaning and provenance

At an embedding index `j` the infinitesimal character of highest weight
`μ_j = (μ_{j,1} ≥ … ≥ μ_{j,n})` is `μ_j + ρ`, with entries `μ_{j,i} + (n + 1)/2 − i`;
these are the weights of the archimedean parameter at that embedding. Consecutive
entries differ by `μ_{j,i} − μ_{j,i+1} + 1`. So `μ_j` is strictly decreasing exactly
when these weights are at distance at least `2` from one another. Henniart 2001,
§5.5, Remark (printed p. 179), states algebraicity and regularity as "same
infinitesimal character as an algebraic representation of `Res_{F/ℚ} GL_n`" and
"regular infinitesimal character". That is the published `IsRegularAlgebraic`; the
regularity of the highest weight defined here is stronger.

Regular highest weight is the hypothesis of Kottwitz 1992, remark after Theorem 1
(printed p. 658): by the work of Vogan and Zuckerman, the cohomology of his Shimura
varieties then lies in the degree `dim S_K` alone. Kottwitz's groups (§1, printed
pp. 654–655) allow products of unitary groups of signatures `(n(i), n(i'))` with
`n(i) + n(i') = n` at the real places; a factor of signature `(p, q)` contributes `pq` to
`dim S_K`, half the dimension of its noncompact tangent space. The construction of
Harris's Proposition 4.8 uses the signature of Clozel 1991, Hypothèse 5.1 (printed
p. 131): `(n − 1, 1)` at one real place and definite at the others, so that
`dim S_K = n − 1`. For that signature the argument is that of Vogan and Zuckerman 1984
applied to the semisimple group `SU(n − 1, 1)` of the noncompact archimedean factor, to
which one passes from Kottwitz's similitude group by removing the similitude factor,
the compact factors and the centre. By their Theorem 5.6 (printed p. 75), an irreducible unitary
representation with nonzero relative Lie algebra cohomology with coefficients in the
irreducible finite-dimensional representation `F` is an `A_q(λ)`, and the Levi factor
`L` of the `θ`-stable parabolic `q = l + u` acts on `F / uF` by a one-dimensional
unitary character. Its differential is, up to sign, an extremal weight of `F`, which
therefore vanishes on the coroots of `l`. When the highest weight of `F` is regular,
every extremal weight is regular and vanishes on no coroot, so `l` is a Cartan
subalgebra; like every `θ`-stable Levi factor in Vogan and Zuckerman's construction it
contains a Cartan subalgebra of `k`. For `SU(n − 1, 1)` a Cartan
subalgebra of `k` is a Cartan subalgebra of `g` (the group has a compact Cartan
subgroup), so `l` is contained in `k` and `l ∩ p = 0`. In Theorem 5.5 (printed p. 74)
the cohomology in degree `i` is `Hom_{L ∩ K}(∧^{i − R}(l ∩ p), ℂ)`, which is
therefore nonzero only for `i = R = dim(u ∩ p) = ½ dim p = n − 1`, where it is
one-dimensional.

The compact Cartan subalgebra is needed. For a group without one, regular highest
weight does not force concentration in one degree: for `SL₂(ℂ)` regarded as a real
group, a `θ`-stable Borel subalgebra and a regular coefficient highest weight of the
form `(m, m)`, `m > 0`, give a unitary `A_q(λ)` with `l ∩ p` of dimension one and
cohomology in two consecutive degrees.

These theorems are cited for orientation only. This module states and proves nothing
about cohomology.

## Sources

- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor.
  Nombres Bordeaux 13 (2001), §5.5, Remark, printed p. 179 (PDF p. 14). Registered
  `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
- D. A. Vogan, Jr. and G. J. Zuckerman, *Unitary representations with non-zero
  cohomology*, Compositio Math. 53 (1984), Theorems 5.5 and 5.6, printed pp. 74–75
  (PDF pp. 25–26). Registered `vogan-zuckerman-1984-unitary-nonzero-cohomology`,
  SHA256 `ccaaf5ad243ccb85d3db629ff7677ca5b80b7e2d71e502d21fa1b773863b78a4`.
- R. E. Kottwitz, *On the `λ`-adic representations associated to some simple Shimura
  varieties*, Invent. Math. 108 (1992), §1, printed pp. 654–655, and remark after
  Theorem 1, printed p. 658.
  Registered `kottwitz-1992-lambda-adic-simple-shimura`, SHA256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- L. Clozel, *Représentations galoisiennes associées aux représentations automorphes
  autoduales de `GL(n)`*, Publ. Math. IHÉS 73 (1991), Hypothèse 5.1, printed p. 131.
  Registered `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
