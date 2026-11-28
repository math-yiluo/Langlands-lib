# Statements on the Lie filtration and the Moy–Prasad isomorphism of tori

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its maximal unramified
extension, `O = fixedFieldIntegers F`, `𝔪` its maximal ideal and `p` the residue
characteristic. For a `K`-torus `T` (`hT : IsTorus T.toGrp`) write

- `T(K)_r = minimalCongruentPoints F T hT r` for the minimal congruent filtration
  (`TorusFiltration.Construction`),
- `t(K)_r = minimalCongruentLie F T hT r`, the Lie lattice of the constructed smooth model
  `𝒯_r`, for the Lie filtration (`TorusFiltration.Lie`),
- `minimalCongruentQuotient F T hT r s = T(K)_r / T(K)_s` and
  `minimalCongruentLieQuotient F T hT r s = t(K)_r / t(K)_s` (`TorusFiltration.MoyPrasad`;
  both quotients are by the intersection with the level-`r` term, which is the level-`s` term
  for `r ≤ s`),
- `minimalCongruentMoyPrasad F T hT h𝔩 hF r s hr hrs hs : T(K)_r / T(K)_s →*
  Multiplicative (t(K)_r / t(K)_s)` for the homomorphism of Kaletha–Prasad, Proposition
  B.10.16, defined for `1 ≤ r ≤ s ≤ r + ⌊r⌋` (`TorusFiltration.MoyPrasad`).

This file states five properties of these objects and their conjunction
`MinimalCongruentMoyPrasadStatements`. It proves none of them. All statements are
universe-polymorphic in `F`.

## Hypotheses common to the statements

- Every torus carries the binder `[IsAffine T.X.left]`, which the constructions of
  `TorusFiltration.Lie` and `TorusFiltration.MoyPrasad` take. It is automatic for a torus
  (`SplittingAssembly.isAffine_of_isTorus`).
- The homomorphism `minimalCongruentMoyPrasad` is built from two results that the Library
  states in `IntegralModel.CongruenceLieStatements` and that are not proved in the modules it
  imports here:
  `h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement` (KP Lemma A.5.13(4)) and
  `hF : IntegralModel.CongruenceLieFunctorialityStatement` (the functoriality in KP
  Proposition A.5.19(3)). The statements about this homomorphism quantify over proofs `h𝔩` and
  `hF`. Since these are proofs of propositions, the homomorphism does not depend on which proofs
  are used, and each statement applies to whatever proofs of the two results are available.

## 1. The Lie filtration — `MinimalCongruentLieFiltrationStatement`

For every `K`-torus `T`:

- `r ↦ t(K)_r` is antitone;
- every `t(K)_r` is a lattice (`Submodule.IsLattice` over `K` in `GenericLie O T.toGrp`);
- `𝔪 • t(K)_r = t(K)_{r+1}` for every `r ≥ 0` (the Lie congruence).

This is the Lie side of KP Propositions B.10.15 and B.10.16: KP define `t(k)_r = Lie(T_r^mc)`
and use `t(k)_{r+1} = 𝔪 t(k)_r`, which follows from KP Lemma A.5.13(4) applied to `T_r^mc` and
the congruence property `T_r^mc(𝔪) = T(K)^mc_{r+1}` (KP Proposition B.10.10).

The module `TorusFiltration.Lie` proves the first two parts (`minimalCongruentLie_antitone`,
`minimalCongruentLie_isLattice`), and the third from KP Lemma A.5.13(4) taken as an argument
(`smul_minimalCongruentLie h𝔩 r 1`). The statement here asserts the third part
unconditionally.

The lattice condition is stated with the tower instance `GenericLie.instIsScalarTower` as a
local instance of high priority: without it the instance search through the intermediate-field
structure of `inertiaFixedField F` does not terminate within the default limits.

## 2. Bijectivity — `MinimalCongruentMoyPrasadBijectiveStatement`

For every `K`-torus `T`, all `h𝔩`, `hF`, and `1 ≤ r ≤ s ≤ r + ⌊r⌋`, the homomorphism
`minimalCongruentMoyPrasad F T hT h𝔩 hF r s hr hrs hs` is bijective. So it is an isomorphism of
abelian groups `T(K)_r / T(K)_s ≅ t(K)_r / t(K)_s`.

This is the isomorphism claim of KP Proposition B.10.16. KP write `r = r₀ + n` with
`0 ≤ r₀ < 1` and `n` a positive integer, and take `r₀ + n ≤ s ≤ r₀ + 2n`. Here `n = ⌊r⌋`, so
the range is `r ≤ s ≤ r + ⌊r⌋`.

## 3. Functoriality — `MinimalCongruentMoyPrasadFunctorialStatement`

For a homomorphism of `K`-tori `f : T ⟶ U`:

- for every `r`, the differential `GenericLie.map O (CommGroupScheme.groupHom f)` maps
  `t(K)_r` into `u(K)_r`;
- for all `h𝔩`, `hF` and `1 ≤ r ≤ s ≤ r + ⌊r⌋`, the square

  ```
  T(K)_r / T(K)_s ──── B.10.16 for T ────→ t(K)_r / t(K)_s
        │                                        │
  minimalCongruentQuotientMap f        minimalCongruentLieQuotientMap f
        ↓                                        ↓
  U(K)_r / U(K)_s ──── B.10.16 for U ────→ u(K)_r / u(K)_s
  ```

  commutes. The left map is induced by `f` on points, which preserves the filtration by its
  functoriality (`minimalCongruentFunctoriality`, KP Proposition B.10.10). The right map is
  induced by the differential of `f`. Both are defined in `TorusFiltration.MoyPrasad`.

This is the functoriality claim of KP Proposition B.10.16. The first part is proved in
`TorusFiltration.Lie` as `map_minimalCongruentLie_le`. It is included so that the statement
records both components of the functoriality claim.

## 4. Corrected KP Proposition B.10.17 — `MinimalCongruentQuotientIsoStatement`

For every `K`-torus `T` and all `r`, `s` with

  `0 < r < s ≤ r + 1` and `s ≤ 2r`,

there exists an isomorphism of abelian groups `T(K)_r / T(K)_s ≅ t(K)_r / t(K)_s`, written
`minimalCongruentQuotient F T hT r s ≃* Multiplicative (minimalCongruentLieQuotient F T hT r s)`.
It is not required to be functorial. (The condition `0 < r` follows from `r < s ≤ 2r`; it is
kept to match KP.)

### KP's statement is false

KP Proposition B.10.17 claims the isomorphism for all `0 < r < s ≤ r + 1`. This fails for wildly
ramified tori.

Take `F = Q_2`, so `K = Q_2^ur`, and let `L = K(i)`, `i² = −1`. The extension `L/K` is totally
ramified of degree `e = 2`, with uniformizer `ϖ = i − 1`. Let `T = R_{L/K} G_m`, with
`T(K) = L^×`, and let `v_L` be the normalized valuation of `L`. Since `T` is induced, its minimal
congruent filtration is its standard filtration (KP Corollary B.10.13), and its Lie filtration
is the Lie filtration of the standard models (KP Proposition B.6.9 and its proof):

  `T(K)_r = U_L^{⌈2r⌉} = {x ∈ O_L^× : v_L(x − 1) ≥ 2r}`,  `t(K)_r = 𝔪_L^{⌈2r⌉}`.

Take `r = 1/2` and `s = 3/2`, so `0 < r < s = r + 1`. Then:

- `T(K)_r / T(K)_s = U_L^1 / U_L^3`. Here `i ∈ U_L^1` and `i² = −1` with `v_L(−1 − 1) =
  v_L(2) = 2`, so `i² ∈ U_L^2 ∖ U_L^3`. The class of `i` has order 4.
- `t(K)_r / t(K)_s = 𝔪_L / 𝔪_L^3`. It is killed by 2, since `2 𝔪_L = 𝔪_L^3`.

A group with an element of order 4 is not isomorphic to a group killed by 2, so no isomorphism
exists.

KP's proof of Proposition B.10.17 uses Proposition B.10.12, that the special fibre of `T_r^mc`
is a vector group for `r > 0`. Here the special fibre of `T_{1/2}^mc` has group of points
`T(K)_{1/2} / T(K)_{3/2} = U_L^1 / U_L^3` (by the congruence property). This group is not killed
by 2, so the fibre is not a vector group. The gap is in the proof of Proposition B.10.12: a
smooth connected commutative unipotent group over a perfect field need not be a vector group
(the Witt group `W_2` is an example), so unipotence alone does not suffice.

### The condition `s ≤ 2r` is sharp

The same construction shows that no weaker condition on `(r, s)` works uniformly. Let
`0 < r < 1` and `2r < s ≤ r + 1`. Choose an integer `e` with `e(1 − r) ≥ 1` and
`e(s − 2r) > 2`. Let `L = K(2^{1/e})` over `K = Q_2^ur`, totally ramified of degree `e` (the
polynomial `X^e − 2` is Eisenstein), and `T = R_{L/K} G_m`, so that
`T(K)_r = U_L^{⌈er⌉}` and `t(K)_r = 𝔪_L^{⌈er⌉}`. Put `a = ⌈er⌉`, so `1 ≤ a < e`. Then:

- `x = 1 + ϖ^a ∈ T(K)_r` has `v_L(x² − 1) = v_L(2ϖ^a + ϖ^{2a}) = 2a`, because
  `2a < e + a = v_L(2ϖ^a)`. Also `⌈es⌉ > 2a`, because `es > 2er + 2 > 2a`. So `x² ∉ T(K)_s`.
- `t(K)_r / t(K)_s = 𝔪_L^a / 𝔪_L^{⌈es⌉}` is killed by 2, because
  `2 𝔪_L^a = 𝔪_L^{a+e}` and `⌈es⌉ ≤ ⌈er⌉ + e = a + e`.

For `r ≥ 1` the condition `s ≤ 2r` follows from `s ≤ r + 1`. So within KP's range
`0 < r < s ≤ r + 1`, the statement holds uniformly over all `F` and `T` exactly for `s ≤ 2r`.

### Why the corrected statement holds (argument on paper, not formalized)

- If `r ≥ 1`, then `s ≤ r + 1 ≤ r + ⌊r⌋`, and the homomorphism of KP Proposition B.10.16 is an
  isomorphism (statement 2).
- If `r < 1`, then `T(K)_r / T(K)_s` is killed by `p`. By KP Definition B.10.8(2), `T(K)_r` is
  generated by the images of `R(K)^std_r` under homomorphisms `R → T` from induced tori `R`, and
  by the first congruence subgroup `T(K)_1` of the connected Néron model. For `x = 1 + y` in the
  standard filtration of `R_{E/K} G_m` with `ord(y) ≥ r`, one has
  `ord(x^p − 1) ≥ min(r + 1, pr) ≥ s`, and the images of `R(K)^std_s` lie in `T(K)_s`. For
  `y ∈ T(K)_1`, the quotient `T(K)_1 / T(K)_2` is an `f`-vector space (KP Proposition A.5.19),
  so `y^p ∈ T(K)_2 ⊆ T(K)_s`, using `s ≤ r + 1 < 2`. Also `t(K)_r / t(K)_s` is killed by `𝔪`, since
  `𝔪 t(K)_r = t(K)_{r+1} ⊆ t(K)_s`. By KP Proposition B.10.15, `T(K)_r / T(K)_s` is the group of
  points over the algebraically closed residue field `f` of the cokernel `Q` of
  `T_s^mc → T_r^mc` on special fibres. `Q` is a smooth connected commutative unipotent group
  with `dim Q = dim_f t(K)_r / t(K)_s`. Being killed by `p` over a perfect field, `Q` is a vector
  group, so `Q(f) ≅ Lie(Q) = t(K)_r / t(K)_s`. KP's argument then applies, including
  compatibility with `Gal(K/F)` when `T` comes from `F`.

## 5. Galois compatibility — `MinimalCongruentMoyPrasadGaloisStatement`

Let `S` be an `F`-torus (`hS : IsTorus S.toGrp`), `T = torusUnramifiedBaseChange F S` its base
change to `K`, and `hT = IsTorus.baseChange hS`. As in `TorusFiltration.GaloisStatements`, the
statement carries the binder `[IsAffine (torusUnramifiedBaseChange F S).X.left]`. The group
`Gal(K/F) = (K ≃ₐ[F] K)` acts through the coefficients:

- on `T(K)` by `rationalConjugate F K S.toGrp σ` (`GaloisPointRational`);
- on the Lie algebra `GenericLie O T.toGrp` by the semilinear map
  `Lie.baseChangeGaloisEquiv F K S.toGrp σ` (`Lie.WeightSupportGalois`), transported through the
  identity equivalence `GenericLie.equiv O T.toGrp` with the Lie kernel. The statement calls
  this map `σL σ`.

The statement asserts:

1. For all `h𝔩`, `hF`, `1 ≤ r ≤ s ≤ r + ⌊r⌋` and `σ`: if the homomorphism `Φ` of KP
   Proposition B.10.16 sends the class of `g ∈ T(K)_r` to the class of `X ∈ t(K)_r`, then
   `σ g ∈ T(K)_r`, `σL σ X ∈ t(K)_r`, and `Φ` sends the class of `σ g` to the class of
   `σL σ X`.
2. For `0 < r < s ≤ r + 1` with `s ≤ 2r` there is an isomorphism
   `e : T(K)_r / T(K)_s ≅ t(K)_r / t(K)_s` that commutes with every `σ` in the same sense.

Equivariance is stated in this relational form because the two actions are defined on `T(K)`
and on `GenericLie O T.toGrp`, not on the quotients. The statement includes the stability of
`T(K)_r` and `t(K)_r` under `Gal(K/F)` (for `T(K)_r` this is part of
`MinimalCongruentUnramifiedDescentStatement`, KP Remark B.10.15 of the 2024 corrections). This
is KP's compatibility with unramified extensions in Propositions B.10.16 and B.10.17, which
descends both isomorphisms to `F`. Part 2 uses the corrected range of statement 4.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (PDF page = printed page
+ 31):

- Propositions B.10.16 (printed p. 694) and B.10.17 (printed p. 695), with the remarks before
  B.10.16 (printed p. 694);
- Propositions B.10.12 (printed p. 691) and B.10.15 (printed p. 693), Corollary B.10.13
  (printed p. 692), Definition B.10.8 and Proposition B.10.10 (printed p. 690);
- Proposition B.6.9 (printed p. 673), Lemma A.5.13(4) (printed pp. 636–637) and Proposition
  A.5.19 (printed pp. 641–643).

Remark B.10.15 is in Kaletha–Prasad, *Corrections and additions in the book "Bruhat–Tits
theory: a new approach"*, registered as `kaletha-prasad-2024-corrections`, version of
1 November 2024, PDF p. 50, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. Its Section B.10 does not
change Propositions B.10.12 or B.10.17.
