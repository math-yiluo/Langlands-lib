# Maximality of the standard compact subgroup of the actual adelic `GL(n)`

This module proves that the standard compact subgroup `standardCompact F n` of the actual
adelic group `AdelicGL F n = GL(n, 𝔸_F)` is a maximal compact subgroup: every compact
subgroup of `AdelicGL F n` that contains it is equal to it. It then transports this to the
actual adelic points of the general linear group scheme over `F`, in the Library predicate
`AdelicGroupPoints.IsMaximalCompactSubgroup`. Here `F : Type u` is an arbitrary number field
and `n : ℕ` is arbitrary, including `n = 0`. The adele ring is the full
`Adeles F = AdeleRing (𝓞 F) F` with its actual topology. "Compact" always means compact as a
subset in the actual topology of the ambient group, and maximality is among all compact
subgroups of that group.

`standardCompact F n` is defined in `Langlands.Global.AdelicGLStandardCompact` (accepted
candidate, bundled unchanged here). It is the set of `g` whose infinite component lies in the
Library's `standardInfiniteCompact F n`, which is real orthogonal at each real place and
complex unitary at each complex place, and whose finite component lies in
`FiniteAdelicGL.standardIntegral F n`, where `g` and `g⁻¹` have integral entries at every
finite place.

## Provenance

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`:

* §2.7, Theorem 2.7.1, printed p.71 (PDF p.88): "There exists a maximal compact subgroup
  `K ≤ G(A_F)` such that `G(A_F) = P(A_F)K`." The same page chooses such a `K` for Siegel
  sets. The Library target `AdelicGoodSiegelReductionStatement` asks for compact data whose
  compact subgroup satisfies `IsParabolicIwasawaCompact`, which includes
  `IsMaximalCompactSubgroup`. This module supplies the maximality part for `GL(n)` and the
  explicit subgroup `standardCompact F n`. It does not prove the covering
  `G(𝔸_F) = P(𝔸_F) K`.
* §2.4, Theorem 2.4.3 and Example 2.2, printed p.59 (PDF p.76). Theorem 2.4.3 states that
  `𝒢(O_F)` is a maximal compact subgroup of `G(F)` for a model `𝒢` with reductive special
  fiber over a non-archimedean local field `F`. Example 2.2 says that for `G = GL_n`,
  `GL_n(O_F)` is a hyperspecial subgroup of `GL_n(F)`. Together they give that `GL_n(O_F)`
  is maximal compact in `GL_n(F)`. `localIntegral_maximal` is this statement at each finite
  completion of `F`. The book cites Bruhat–Tits for Theorem 2.4.3. The proof here is
  elementary and different (see below).

The October 2026 errata (`getz-hahn-2024-errata-2026-10`) list no corrections for
Chapter 2. The archimedean maximality is the Library theorem
`standardInfiniteCompactMaximality`, imported as is. The global statement and its assembly
from the local ones are derived. The gauge `supGauge` and the general lemma
`mem_of_isCompact_of_integral_le` are internal to this proof.

## Compact overgroups of the integral matrices over a normed field

Let `𝕜` be a normed field and `H` a subgroup of `GL (Fin n) 𝕜`. We use the sup norm on
`Fin n → 𝕜`.

* `supGauge H x` is the real number `⨆ h : H, ‖h *ᵥ x‖`. For compact `H` the supremum is over
  a bounded set (`bddAbove_supGauge`, by continuity of `g ↦ ‖g *ᵥ x‖`). In that case
  `le_supGauge` gives `‖x‖ ≤ supGauge H x`, taking `h = 1`.
* `supGauge_mulVec hk x`: if `k ∈ H` then `supGauge H (k *ᵥ x) = supGauge H x`, because right
  multiplication by `k` permutes `H`.
* `supGauge_smul c x`: `supGauge H (c • x) = ‖c‖ * supGauge H x`.
* `mem_of_isCompact_of_integral_le O hO hH hle hh a j` is the key lemma. Let `O` be a
  subring of `𝕜` whose elements are exactly the `x` with `‖x‖ ≤ 1`. Let `H` be compact and
  contain every `g` such that `g` and `g⁻¹` have all entries in `O`. Then every entry
  `h a j` of every `h ∈ H` lies in `O`.

  Proof. Let `e` be the `j`-th standard basis vector and `y = h *ᵥ e`, the `j`-th column of
  `h`. Choose `i₀` maximizing `‖y i‖` and put `c = y i₀`. Then `c ≠ 0`, since otherwise
  `y = 0` and `e = h⁻¹ *ᵥ y = 0`. The vector `z = c⁻¹ • y` has entries in `O` and
  `z i₀ = 1`. Let `A` be the identity matrix with column `i₀` replaced by `z`, then with
  columns permuted by the transposition `(i₀ j)`. Then `A *ᵥ e = z`, the entries of `A` lie
  in `O`, and `det A = ± z i₀ = ± 1`. So `A⁻¹` also has entries in `O` (by the adjugate
  lemma `inv_mem_of_forall_mem` of `AdelicGLStandardCompact`), and hence `A ∈ H`. By
  invariance and homogeneity,
  `supGauge H e = supGauge H y = supGauge H (c • z) = ‖c‖ * supGauge H z = ‖c‖ * supGauge H e`.
  Also `supGauge H e ≥ ‖e‖ ≥ 1 > 0`, so `‖c‖ = 1`. Hence `‖h a j‖ = ‖y a‖ ≤ ‖c‖ = 1`.

## Finite places

* `localIntegral_maximal F n v H hH hle`: at a finite place `v`, let `H` be a compact
  subgroup of `FiniteLocalGL F n v = GL(n, F_v)` containing
  `(FiniteAdelicGL.localIntegral F n v).toSubgroup`, which is `GL(n, O_v)`: the matrices `g`
  such that `g` and `g⁻¹` have entries in the completion integers. Then `H` equals that
  subgroup. The integers of the completion are exactly the elements of norm at most `1`
  (`Valued.toNormedField.norm_le_one_iff`). So the key lemma applies to `h` and to `h⁻¹`
  for every `h ∈ H`.

## Assembly

* `standardCompact_maximal F n L hL hle`: let `L` be a compact subgroup of `AdelicGL F n`
  with `standardCompact F n ≤ L`. Then `L = standardCompact F n`. Proof: take `g ∈ L`.
  - The image of `L` under the continuous infinite projection `AdelicGL.infinite F n` is a
    compact subgroup. It contains `standardInfiniteCompact F n`, because `κ` is the image of
    `AdelicGL.pair F n κ 1 ∈ standardCompact F n`. By the Library's
    `standardInfiniteCompactMaximality` the image equals `standardInfiniteCompact F n`, so
    the infinite component of `g` lies there.
  - Fix a finite place `v`. The image of `L` in `FiniteLocalGL F n v`, under the finite
    projection followed by `FiniteAdelicGL.localProjection F n v`, is a compact subgroup.
    It contains `GL(n, O_v)`, because `k` is the image of
    `AdelicGL.pair F n 1 (FiniteAdelicGL.localInclusion F n v k) ∈ standardCompact F n`
    (`FiniteAdelicGL.localInclusion_mem_standardIntegral`). By `localIntegral_maximal` the
    image equals `GL(n, O_v)`. So the local component of `g` at `v` lies there, and
    `FiniteAdelicGL.mem_standardIntegral_iff_local` puts the finite component of `g` in
    `standardIntegral`.

  Hence `g ∈ standardCompact F n`, and the reverse inclusion is `hle`.
* `isMaximalCompact_standardCompact F n`: `CompactIwasawa.IsMaximalCompact (standardCompact F
  n)`. This combines `isCompact_standardCompact` with `standardCompact_maximal`.
* `isMaximalCompactSubgroup_generalLinear F n`: the image of `standardCompact F n` under the
  inverse of the Library's multiplicative homeomorphism
  `GeneralLinearGroupPoints.adelicHomeomorph F n` satisfies
  `AdelicGroupPoints.IsMaximalCompactSubgroup F (GroupScheme.GeneralLinear.groupScheme (Fin n)
  (CommRingCat.of F))`. Here `adelicHomeomorph F n` maps the actual adelic points of the
  `GL_n` group scheme to `AdelicGL F n`. The proof is `CompactIwasawa.IsMaximalCompact.map`.

## Scope

No Iwasawa covering `G(𝔸_F) = P(𝔸_F) K`, conjugacy of maximal compact subgroups,
uniqueness, or statement about groups other than `GL(n)` is asserted. The general reductive
reduction target remains open.
