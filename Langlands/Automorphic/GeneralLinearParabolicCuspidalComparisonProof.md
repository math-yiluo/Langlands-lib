# All-proper and standard maximal-block GL cuspidality agree

This module proves the Library statement
`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearParabolicCuspidalComparisonStatement`
(module `Langlands.Automorphic.GeneralLinearParabolicCuspidalComparisonStatement`)
in the universe `u` of the statement, by the theorem
`Langlands.Automorphic.GroupSchemeFunctions.generalLinearParabolicCuspidalComparison`.
A closing `example` checks its type against the statement.

The statement fixes a number field `F`, `n : ℕ`, the dynamic-parabolic input
`hPD : ParabolicDynamicStatement.{u}`, connected reductivity `hG` of
`G = GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`, and
compactness of `𝔸_F / F`. It asks for equality of two subrepresentations of
continuous functions on `G(F) \ G(𝔸_F)`:

- `normalizedParabolicCuspidalSubrepresentation F G hPD hG`: for every proper
  rational parabolic `P`, the constant term along the radical
  `properRationalParabolicRadicals hPD hG P` vanishes at every point. The
  constant term uses the mass-one Haar quotient measure
  `normalizedRationalQuotientHaarMeasure`.
- `generalLinearStandardBlockVanishingSubrepresentation F n`: the classical
  constant terms along the unipotent radicals of the standard maximal block
  parabolics `(a, b)`, `a + b = n`, `0 < a`, `0 < b`, vanish.

The proof adds no hypothesis. The inclusion `≤` is the published
`normalizedGeneralLinearParabolicCuspidal_le_standardBlock`. The proof of the
reverse inclusion `≥` occupies the rest of this module.

## Haar-domain form of normalized vanishing

The proof reuses Worker 1635's published theorem
`normalizedConstantTerm_eq_zero_iff_fundamentalDomainIntegral_eq_zero` from
`Langlands.Automorphic.GroupSchemeConstantTermFundamentalDomain`. For any affine
group scheme over `F` of locally finite type, a subgroup functor with closed
adelic points and finite intrinsic quotient mass, it identifies vanishing of
the normalized constant term with vanishing of the Haar integral over the
chosen rational fundamental domain. Unfolding `fundamentalDomainConstantTerm`
gives the literal integral used by the semidirect period theorem.

The module's local Borel instance now has the distinct name
`fundamentalDomainQuotientBorelSpace`, so this proof can import it together with
`GeneralLinearConstantTermComparison` and reuse the public result directly.

## Proper parabolics are conjugate to block parabolics

Write `U_e = blockUnipotent (Fin n) (CommRingCat.of F) e` for a weight
`e : Fin n → ℤ`. Its matrices `x` satisfy `x i j = δ i j` whenever `e i ≤ e j`.

- `blockParabolic_eq_top_of_forall_le`: if `e` has no strict increase, every
  invertible matrix satisfies the block parabolic condition, so
  `blockParabolic (Fin n) _ e = ⊤`.
- `exists_properRationalParabolicRadicals_eq_comap`: for every proper rational
  parabolic `P` there are a rational point `g` and a weight `e` with a strict
  increase `e i < e j`, such that the radical of `P` is
  `U_e.comap (G.innerIso g).hom`. The proof takes a cocharacter `χ` with
  `Dynamic.parabolic χ = P` (`exists_dynamicCocharacter`) and conjugates it to
  the diagonal cocharacter of `e` (`exists_innerIso_comp_eq_diagonalCocharacter`).
  By `Dynamic.parabolic_eq_comap_of_iso` and `parabolic_diagonalCocharacter`,
  `P` is the inverse image of `blockParabolic e`. If `e` had no strict
  increase, `P` would be `⊤`, contradicting properness. The radical is
  `Dynamic.unipotent χ` (`rationalParabolicRadical_eq_dynamic`), which
  `Dynamic.unipotent_eq_comap_of_iso` and `unipotent_diagonalCocharacter` turn
  into `U_e.comap (G.innerIso g).hom`.

## Vanishing along block unipotent subgroups

`forall_constantTerm_blockUnipotent_eq_zero`: let `f` lie in the standard
maximal-block vanishing subrepresentation, let `e i < e j`, and let the rational
quotient of `U_e` be compact. Then every normalized constant term of `f` along
`U_e` vanishes. The proof has four steps.

1. Threshold weight. Let `w = thresholdWeight e (e i)`, which is `1` where
   `e i < e k` and `0` elsewhere. It is weakly increasing in `e`
   (`thresholdWeight_le_of_le`), so `U_w` is the normal factor of `U_e` used in
   `Langlands.Global.GeneralLinearBlockSemidirect`.
2. Standard maximal block. `exists_perm_thresholdWeight_eq_twoBlockWeight` gives
   `a + b = n` and a permutation `τ` that carries `w` to the standard two-block
   weight. Here `0 < a` because of `j` and `0 < b` because of `i`.
   `hasVanishingConstantTerm_generalLinearBlock_intrinsic_iff` and
   `mem_generalLinearStandardBlockVanishingSubrepresentation_iff` turn the
   hypothesis on `f` into vanishing of every normalized constant term along the
   standard subgroup `GeneralLinearBlockUnipotent.subgroup F h`.
3. Permutation conjugation. `blockUnipotent_eq_comap_innerIso_permPoint`
   writes `U_w` as the inverse image of the standard subgroup under the inner
   automorphism of a permutation matrix. `forall_constantTerm_eq_zero_comap_innerIso_iff`
   then gives vanishing of every normalized constant term along `U_w`.
4. Semidirect period. The published theorem above turns the goal and each
   constant term along `U_w` into fundamental-domain integrals. Both quotients
   have finite mass by `rationalQuotientHaarMeasure_isFiniteMeasure`; the
   quotient of `U_w` is compact by `thresholdRationalQuotientCompactSpace`.
   `GeneralLinearBlockSemidirect.integral_fundamentalDomain_eq_zero` applies to
   `φ x = f(x y)`. `φ` is continuous, and it is left invariant under rational
   points of `U_e` because `f` is left `G(F)`-invariant. Its hypothesis asks
   that the `U_w` period of `φ` vanish on every translate by an adelic point `m`
   of the Levi part. That period is the `U_w` integral of `f` at `m y`, after
   reassociating `(z m) y = z (m y)`, so it vanishes by step 3.

## The final theorem

`generalLinearParabolicCuspidalComparison` proves `≥` as follows. Take `f` in
the standard vanishing subrepresentation and a proper rational parabolic `P`.
Then `exists_properRationalParabolicRadicals_eq_comap` gives `g` and `e`. The
subgroup `U_e` is the inverse image of the radical under the inverse inner
automorphism. Its rational quotient is therefore compact, by
`rationalQuotientCompactSpace_comap` and the published compactness of the
radical quotients. `forall_constantTerm_blockUnipotent_eq_zero` gives vanishing
along `U_e`, and `forall_constantTerm_eq_zero_comap_innerIso_iff` moves it to
the radical of `P`.

## Dependencies

The module imports the target statement module and the published Library
modules `Langlands.Automorphic.GeneralLinearParabolicCuspidalInclusion`,
`Langlands.Automorphic.GroupSchemeConstantTermConjugation`,
`Langlands.Automorphic.GroupSchemeConstantTermFundamentalDomain`,
`Langlands.Automorphic.GroupSchemeDynamicParabolicRadical` and
`Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal`. It also imports
`Langlands.Global.GeneralLinearBlockSemidirectPeriod`, which is new in this
contribution and has its own Markdown.

The block semidirect module uses Worker 1635's abstract period theorem
`Langlands.Global.LeftCosetSpace.Semidirect.integral_fundamentalDomain_eq_zero_of_compact`.
Worker 94's `Langlands.Global.AdelicSubgroupQuotientTransport` supplies the
transport of quotients along rational conjugation.
