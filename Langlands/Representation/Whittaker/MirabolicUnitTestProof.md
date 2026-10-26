# Compact opposite-character mirabolic test functions: proof

Author: Worker 11.

This module proves the published proposition
`Langlands.Whittaker.MirabolicUnitTestStatement.{uF} F T n` of
[MirabolicUnitTestStatement](MirabolicUnitTestStatement.md). It changes
neither that statement nor anything it imports. The closing theorem
`Langlands.Whittaker.mirabolicUnitTest` has the complete type

`∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
  Langlands.Whittaker.MirabolicUnitTestStatement F T n`.

The field universe `uF` stays arbitrary. The proof uses the supplied
realization `T` throughout and covers every unitary additive character. The
rank-one case `n = 0` needs no separate argument. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The module also adds a small group-theoretic helper in the namespace
`Langlands.Whittaker.MirabolicUnitTest`, described next.

## Generic coset extension

Let `G` be any group, `N` and `H` subgroups of `G`, and `θ : N →* ℂˣ`.
The definition `MirabolicUnitTest.cosetExtension N H θ : G → ℂ` takes the
value `θ u` at `g` when some `u : N` satisfies `u⁻¹ g ∈ H`. Here `u` is the
witness picked by `Classical.choose`. At every other `g` the value is `0`.
In other words, `g` has a nonzero value only if it lies in `N H`.

Four theorems hold under the hypothesis `hθ`: `θ u = 1` for every `u : N`
whose image lies in `H`, i.e. `θ` is trivial on `N ∩ H`.

- `cosetExtension_mul hθ u hk`: for `u : N` and `k ∈ H`, the value at `u k`
  is `θ u`. If `v` is the chosen witness for `u k`, then `v⁻¹ u` lies in
  `N ∩ H`, so `θ (v⁻¹ u) = 1` and `θ v = θ u`. Thus the value does not depend
  on how the point is written as a product.
- `cosetExtension_eq_zero`: the function is zero at every `g` that is not of
  the form `u k` with `u : N` and `k ∈ H`. This one needs no hypothesis.
- `cosetExtension_left hθ u g`: the value at `u g` equals `θ u` times the
  value at `g`. If `g = v k` with `v : N` and `k ∈ H`, this follows from
  `cosetExtension_mul` and `θ (u v) = θ u θ v`. Otherwise `u g` is not in
  `N H` either, and both sides are zero.
- `cosetExtension_right hθ g hk`: the function is right invariant under each
  `k ∈ H`. This follows from `cosetExtension_mul` on `N H`, and both sides
  are zero off `N H`.

## The construction

Write `G = GeneralLinear (n + 1) F.Carrier`, `P` for the actual mirabolic
subgroup, `N` for the actual upper-unipotent subgroup and
`χ = standardCharacter ψ n`, as in the statement. The proof installs
`T.topology`, `T.valuativeRel` and `T.localField`, as the statement does.
It also installs the published Hausdorff certificate
`Langlands.PadicField.TopologicalData.fieldT2 T`, a theorem about the same
supplied topology, so it adds no hypothesis.

1. *Open kernel of the standard character.* Install
   `T.upperUnipotentNonarchimedean (n + 1)` on `N`, from `Group.GL.CompactOpen`.
   Then `Langlands.isOpen_ker_of_continuous_complex_character`, applied to
   the continuity of `Whittaker.standardCharacterContinuous ψ n`, makes
   `ker χ` open in `N`. The topology of `N` is induced from `G`, so
   `Topology.IsInducing.subtypeVal.nhds_eq_comap` gives an identity
   neighbourhood `O` of `G` whose preimage in `N` lies in `ker χ`.
2. *Ambient compact open subgroup.* Let `U` be the intersection of `O` with the
   kernel of the normalized determinant norm `T.determinantNorm (n + 1)`.
   That kernel is open by `TopologicalData.isOpen_ker_determinantNorm`, so `U`
   is an identity neighbourhood. `T.generalLinearCompactOpen (n + 1) U`
   chooses a compact open subgroup `J₀` of `G` contained in `U`. It is the
   last existential witness; the order is `P₀`, `φ`, `φ'`, `J₀`.
3. *Mirabolic subgroup.* Set `P₀ = OpenSubgroup.comap P.subtype J₀`, the
   preimage of `J₀` under the continuous inclusion `P → G`. Let
   `H = J₀ ⊓ P` as a subgroup of `G`. Every `k : P₀` has image in `H`.
4. *Functions.* If `u : N` has image in `H`, that image lies in
   `J₀ ⊆ U ⊆ O`, so `χ u = 1`.
   Hence `(inverseStandardCharacter ψ n) u = (χ u)⁻¹ = 1` as well. So both
   characters satisfy the hypothesis `hθ` above. The witnesses are
   `φ = cosetExtension N H χ` and `φ' = cosetExtension N H (inverseStandardCharacter ψ n)`.
   `cosetExtension_left` puts them in the published subtypes
   `RankinSelberg.WhittakerFunctions ψ n` and
   `RankinSelberg.InverseWhittakerFunctions ψ n`.

## The seven clauses

- *`P₀` compact.* `GeneralLinear.Mirabolic.isClosed` says `P` is closed in `G`;
  this lemma uses the Hausdorff certificate. So `P → G` is a closed embedding,
  and the preimage `P₀` of the compact set `J₀` is compact.
- *`J₀` compact.* This is the compactness supplied by
  `generalLinearCompactOpen`.
- *Determinant norm one.* Each `k : P₀` has image in `J₀ ⊆ U`, which lies in
  the kernel of `T.determinantNorm (n + 1)`.
- *Ambient intersection.* If `j ∈ J₀` and `j ∈ P`, then `⟨j, _⟩ : P` lies in
  `P₀` by definition of the preimage. So `j` is in the image `C` of `P₀`.
- *Prescribed values.* For `u : N` and `k : P₀`, `cosetExtension_mul` gives
  `φ (u k) = χ u` and `φ' (u k) = (χ u)⁻¹`. The second value is converted
  from a unit inverse to a complex inverse by `Units.val_inv_eq_inv_val`.
- *Vanishing off `S`.* If `g = u k` with `u : N` and `k ∈ H`, then `k ∈ P` and
  `k ∈ J₀`, so `k` is the image of an element of `P₀` and `g ∈ S`. Hence
  every `g ∉ S` lies outside `N H`, and `cosetExtension_eq_zero` makes both
  functions vanish there.
- *Right `P₀` invariance.* The images of elements of `P₀` lie in `H`, so this is
  `cosetExtension_right`, at every `g : G`.

## Comparison with the suggested route and the source

The statement's Markdown suggests choosing `P₀` small in `P` first and then
`J₀` with `J₀ ∩ P ⊆ P₀`. The implemented proof chooses `J₀` first, inside the
character-kernel and determinant-norm-one neighbourhood. It then takes
`P₀` to be exactly the mirabolic part of `J₀`. This makes the ambient
intersection clause hold by definition. It also needs no separate
nonarchimedean or compact-open theory for the mirabolic group: compactness of
`P₀` comes from closedness of `P`.

JPSS (H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), source ID
`jpss-1983-rankin-selberg`) uses such functions on printed p.393 (one-based
PDF page 28). There, in the equal-rank case, it takes `φ ∈ 𝒦₀(ψ)` and
`φ' ∈ 𝒦₀(ψ̄)` and says one "may choose `φ` and `φ'`" making the remaining
integral over `N_r \ P_r` equal to one. On p.386 (§2.2) it defines `𝒦₀(ψ)` as
the smooth functions on `P_r` that are `θ`-covariant on the left under `N_r`
and compactly supported modulo `N_r`. Page 385 (§2.1) records the passage from
`ψ` to `ψ̄`. JPSS gives no explicit construction of these functions. The
compact open data built here are an internal construction for that choice;
they are not a separately stated JPSS theorem. The Lean proof does not follow
any argument from the source. Worker 11 re-read these three pages visually
in the retained file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`
(SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`);
their content is as the statement's Markdown describes.

## Downstream use

The clauses proved here supply the hypotheses of
`Langlands.Whittaker.isMirabolicTestFunction_of_compact_mirabolic_support` in
the published `Whittaker.MirabolicUnitTestCompatibility`, with `K = P₀` and
`J = J₀`. This module does not import that file. It defines no competing
`IsMirabolicTestFunction` predicate and proves no Kirillov lift,
last-row test, quotient measure or unit-integral identity.
