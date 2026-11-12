# Siegel coverage from Springer's compactness and chamber reduction theorems

Author: Worker 4149 (formerly Worker 0).

This module splits the analytic coverage in the Library predicate `IsSiegelCover` into two
classical theorems of reduction theory, states both as propositions, and proves that they
give the coverage. It proves neither proposition. Compactness of the unipotent rational
quotient, the third ingredient, comes from published proofs.

## The two statements

Both statements quantify, in universe `u`, over every number field `F : Type u` and every
group scheme `G` over `Spec F` with `IsAffineHom G.X.hom`, `LocallyOfFiniteType G.X.hom`
and `IsConnectedReductive G`. `G(𝔸_F)¹` is the Library's `normOneSubgroup F G`, the
intersection of the kernels of the normalized idelic norms of all `F`-rational characters,
and `G(F)` acts through the principal map `rational F G` (or `rationalNormOne F G` into
`G(𝔸_F)¹`).

### `CentralSplitCompactQuotientStatement`

For every commutative group scheme `S` and every `s : S.toGrp ⟶ G` with
`IsMaximalSplitTorus s` and `IsCentral s`, there is a compact set
`Ω ⊆ normOneSubgroup F G` such that every `g ∈ G(𝔸_F)¹` has a principal rational point
`q ∈ G(F)` with `rationalNormOne F G q * g ∈ Ω`. Equivalently, `G(F) \ G(𝔸_F)¹` is the image
of a compact set, hence compact.

*Provenance (derived).* Springer, *Reduction theory over global fields* (1994), §2.1,
printed p.212, statement (C): "`C(G)` is compact if and only if `G` is anisotropic
(i.e. `P = G`)", where `P` is the fixed minimal parabolic `k`-subgroup and
`C(G) = G(𝔸)⁰/G(k)` (§1.1, printed p.208). Springer writes `G(𝔸)⁰` for the adeles on which
every `k`-character has idele norm one, which is the Library's `normOneSubgroup`. The
statement is the "if" direction for number fields. Three conventions differ from the
printed text.

- Springer's rational points act on the right. The left-coset form here is the same
  assertion after inversion `g ↦ g⁻¹`.
- Springer phrases compactness of the quotient. The form "a compact set meets every
  coset" is the one he uses in §2.2, Remark (a), printed p.212: "there is a compact set
  `K₁` in `L(A)⁰` such that `L(A)⁰ = K₁.L(k)`".
- Springer's hypothesis is `P = G`. Here the hypothesis is that a maximal split torus is
  central. For connected reductive `G` the two agree: the minimal parabolic containing the
  maximal split torus `S` is all of `G` exactly when `G` has no relative roots, that is,
  when the centralizer of `S` is `G`. The Library expresses the last condition as
  `isCentral_iff_torusCentralizer_eq_top`. Springer applies (C) in Remark (a) to the Levi
  group `L` of `P`, the centralizer of `S`, in which `S` is a central maximal split torus.
  `exists_leviCompactCover_of_setup` below applies the statement in exactly that way.

### `AdelicSiegelChamberReductionStatement`

Fix `T, i, ν, T₀, j` with `IsSiegelAlgebraicSetup F G T i ν T₀ j`, and write
`P = Standard.parabolicScheme i ν ∅`, `N = Standard.unipotentScheme i ν ∅` and
`M = Standard.leviScheme i ν ∅` with their canonical inclusions. For every subgroup `K` of
`G(𝔸_F)` with `IsParabolicIwasawaCompact F G P (Standard.parabolicHom i ν ∅) K` (`K` is a
maximal compact subgroup and `P(𝔸_F) K = G(𝔸_F)`), the statement asserts that there is a
threshold `t : ℝ≥0ˣ` such that for every `g ∈ G(𝔸_F)¹` there are

- a principal rational point `q ∈ G(F)`,
- a point `n ∈ N(𝔸_F)` and a point `m ∈ M(𝔸_F)¹ = normOneSubgroup F M`,
- a point `a` of the intrinsic positive torus `A_{T₀}` lying in
  `PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`, that is,
  `t ≤ normCharacter F T₀ (j ≫ α) a` for every simple relative root `α`,
- and `k ∈ K`,

with `ι_N(n) · ι_M(m) · positiveMap(a) · k = rational(q) · g` in `G(𝔸_F)`. Here `ι_N` and
`ι_M` are the adelic maps of `Standard.unipotentHom i ν ∅` and `Standard.leviHom i ν ∅`, and
`positiveMap F G T i T₀ j` is the published map of `A_{T₀}`. Neither `n` nor `m` is required
to lie in a compact set; that is the role of the other two compactness results.

*Provenance (derived).* Springer (1994), §2.1, printed pp.211–212, statement (F): "If `G`
is isotropic there is `c` with `G(A)⁰ = 𝒮(c).G(k)`". Here `𝒮(c) = K.S(c).P(A)⁰`, `K` is a
compact subset of `G(A)` with `G(A)⁰ = K.(S(A) ∩ G(A)⁰).P(A)⁰` (printed p.211), and `S(c)`
is the set of `s ∈ S(A) ∩ G(A)⁰` with `|α(s)| ≤ c` for all `α ∈ Δ`, the simple roots
defined by `P`. Springer's `S` is the Library's `T` and his `P(A)⁰` is the kernel of
`P(A) → Hom(X(P), ℝ*₊)`. The statement here is obtained from (F) by inversion `g ↦ g⁻¹`,
which turns `|α(s)| ≤ c` into `|α| ≥ 1/c` and puts `G(F)` on the left, together with three
standard rewritings:

1. `P(A)⁰ = N(𝔸_F) · M(𝔸_F)¹`, because the rational characters of `P` are those of its
   Levi group `M`.
2. `T(𝔸_F) ∩ G(𝔸_F)¹` is the product of the norm-one points `T(𝔸_F)¹` and the positive
   part `A_{T₀}` coming from the derived split torus `T₀`. Indeed the setup makes `T` the
   product of `T₀` and a central split component up to a finite kernel, and the positive
   part of that component meets `G(𝔸_F)¹` trivially. `T(𝔸_F)¹` lies in `M(𝔸_F)¹` and is
   central in `M`, and every root has norm one on it, so it is absorbed into the factor
   `m` without changing the chamber.
3. Springer's compact set `K` (after inversion `K⁻¹`) is replaced by the Iwasawa subgroup
   `K` of the statement: by `P(𝔸_F) K = G(𝔸_F)`, `K⁻¹` lies in `C_P · K` for a compact
   `C_P ⊆ P(𝔸_F)`, and moving `C_P` to the left of `A_{T₀}(t)` changes only the
   `N(𝔸_F) M(𝔸_F)¹` factor and the threshold, by a bounded amount.

These rewritings justify the formulation; they are not proved in this module. When `G` is
anisotropic in Springer's sense, there are no simple roots, so the chamber condition is
vacuous, and `A_{T₀}` is trivial; the statement then follows with `q = 1` from
`P(𝔸_F) K = G(𝔸_F)` and the Levi decomposition of `P(𝔸_F)`. So the formulation needs no
case distinction. The weak inequality and the
normalized idelic norm are those of the published `weakSimpleRootChamber`, the same chamber
as in `IsSiegelCover` and Getz–Hahn (2024) (2.26), printed p.71. Getz–Hahn's proof of
their Theorem 2.7.2 (printed p.72) cites Springer and makes the same conversion: "in loc.
cit. the group `G(F)` acts on the right. Thus one has to take an inverse to move `G(F)` to
the left, and this changes the inequality in the analogue of `A_{T₀}(t)` in loc. cit. to
that we used in defining `A_{T₀}(t)`."

## Proved results

**`exists_leviCompactCover_of_setup`.** Given `CentralSplitCompactQuotientStatement` and an
actual setup, there is a compact `Ω ⊆ M(𝔸_F)¹` meeting every left coset of `M(F)`.
*Proof.* `M` is affine (`IsClosedSubgroup.isAffineHom`) and locally of finite type (a closed
immersion followed by the structure map of `G`). The setup's rational Levi clause gives
`IsConnectedReductive M`. The torus lift `torusToStandardLevi : T ⟶ M` is maximal split by
`IsMaximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor`. It is central by
`isCentral_of_range_le_torusCentralizer`: its composite with the Levi inclusion is `i`, and
the range of the inclusion is the standard Levi functor, which the setup identifies with
`torusCentralizer i`. Apply the statement to `M` and this torus.

**`exists_unipotentCompactCover_of_setup`.** For an actual setup, `N` has a compact set of
adelic points meeting every left coset of `N(F)` (`HasCompactRationalCover`). *Proof.* The
setup's geometric unipotent radical clause makes `N` smooth, connected and unipotent, and `N`
is affine as a closed subgroup of `G`. The published
`exists_isCompact_rational_mul_mem_of_split`, with the published proofs
`perfectFieldUnipotentSplit` and `splitUnipotentAffineTorsorStatement`, gives the cover.

**`exists_isSiegelCover_of_chamber`.** Assume both statements. For every `F`, `G`, actual
setup and `K` with `IsParabolicIwasawaCompact`, there are compact factors
`C : CompactFactors F G N M` with `C.compactSubgroup = K` and `t : ℝ≥0ˣ` with
`IsSiegelCover F G T i ν T₀ j C t`. *Proof.* Take `Ω_N` and `Ω_M` from the two lemmas above
and `t` from the chamber statement, and let `C = (Ω_N, Ω_M, K)`. By the published
`IsSiegelAlgebraicSetup.isSiegelCover_iff_translate` it suffices to find, for each
`g ∈ G(𝔸_F)¹`, a rational `q'` with `rational(q') g` in the weak Siegel product. The chamber
statement gives `n m a k = rational(q) g`. Choose `μ ∈ M(F)` with `μ m ∈ Ω_M`; its image `μ_G`
in `G(F)` satisfies `ι_M(μ) = rational(μ_G)` by `rational_naturality`. Since `μ_G` lies in
`M(𝔸_F) ⊆ P(𝔸_F)`, which normalizes `N(𝔸_F)` (`standardParabolicImage_le_normalizer`),
`μ_G ι_N(n) μ_G⁻¹ = ι_N(n'')` for some `n'' ∈ N(𝔸_F)`. Choose `ρ ∈ N(F)` with `ρ n'' ∈ Ω_N`, with
image `ρ_G` in `G(F)`. Then
`rational(ρ_G μ_G q) g = ι_N(ρ n'') · ι_M(μ m) · positiveMap(a) · k`, which lies in the weak
Siegel product by `mem_productSet_iff`; the identity is a group computation from
`n m a k = rational(q) g`.

## Use and remaining obligations

Together with an actual setup (`SiegelAlgebraicSetupExistenceStatement`, module
`Langlands.Global.AdelicSiegelSetupExistence`) and a maximal compact Iwasawa subgroup, such
as the one asserted by the published `AdelicGroupPoints.ParabolicIwasawaStatement` applied
to the minimal parabolic, `exists_isSiegelCover_of_chamber` gives
`AdelicSiegelReductionStatement`. If the Iwasawa subgroup is in addition
`IsPositiveTorusCompatible` (`AdelicCompatibleIwasawaCompactStatement`, module
`Langlands.Global.AdelicCompatibleIwasawaCompact`), the same theorem gives
`AdelicGoodSiegelReductionStatement`, because it keeps the supplied `K` as the compact
subgroup. These compositions are left to the
final proof of task `6adbbc46-4bb2-4c01-843a-d8ded48189f2`. The two statements of this module
remain unproved: compactness (C) is the Godement compactness criterion, and the chamber
reduction is the core of the fundamental set theorem.

## Sources

T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad. Sci. (Math. Sci.)
104 (1994), 207–216, registered as `springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`. Printed page = PDF page
plus 206. Used: §2.1, printed pp.211–212 (PDF pp.5–6), statements (C) and (F) and the
definitions of `K`, `S(c)` and `𝒮(c)`; §2.2, Remark (a), printed p.212 (PDF p.6). The whole
paper was read for this module. No errata note exists for this source.

J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Graduate Texts in
Mathematics 300, Springer, 2024, registered as `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. Used: §2.7,
printed pp.71–72 (PDF pp.88–89), (2.25)–(2.26) and Theorem 2.7.2 with the remark on the
action convention in its proof. The registered October 2026 errata
`getz-hahn-2024-errata-2026-10` make no correction to §2.7.
