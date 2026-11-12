# The Iwasawa height `H_P` on actual adelic points

Author: Worker 3659.

Mœglin–Waldspurger (1995), I.1.4, printed p. 7, use the decomposition `G = P K` to define
`m_P : G(𝔸) → M¹ \ M(𝔸)`, `m_P(u m k) = M¹ m`, and compose it with `log_M` of their equation (4).
This is the height used for Siegel domains, for `φ ↦ φ · m_P^λ` and for Eisenstein series.

This module defines the height for actual adelic points of group schemes over a number field. It
is defined relative to a *supplied* compact subgroup `K` with `P(𝔸_F) K = G(𝔸_F)`. It proves
that the height does not depend on the factorization, and it proves its invariance and
equivariance properties and its Levi form. The module does not prove that such a `K` exists:
that is the Iwasawa decomposition (Getz–Hahn, Theorem 2.7.1), stated in the Library as
`AdelicGroupPoints.ParabolicIwasawaStatement` and still unproved.

## Data

- `F : Type u` is a number field.
- `G` and `P` are group schemes over `Spec F` with affine underlying schemes, and
  `p : P ⟶ G` is a homomorphism whose underlying morphism is a closed immersion
  (instance `IsClosedImmersion p.hom.hom.left`). No reductivity or parabolicity is assumed. In
  the intended use, `P` is a rational parabolic of a connected reductive `G`, for instance a
  standard parabolic `Standard.parabolicScheme i ν θ` with `Standard.parabolicHom i ν θ`.
- `K` is a subgroup of `G(𝔸_F) = AdelicGroupPoints F G`.

The target of the height is the published real character dual
`RealCharacterDual F P = Hom_Z(Rat(P), ℝ)`, with the published logarithmic map
`characterLog F P : P(𝔸_F) → Hom_Z(Rat(P), ℝ)`, `⟨χ, characterLog q⟩ = log |χ(q)|`. That map is
MW's `log_P` (I.1.4, equation (4)). The real dual of a Levi subgroup is reached through the
published `realCharacterDualMap`.

## Iwasawa subgroups

`IsIwasawaCompact p K` is a structure in `Prop` with two fields:

- `isCompact`: `K` is compact in `G(𝔸_F)`;
- `range_mul`: `Set.range (map F P G p) * K = Set.univ`, that is, `P(𝔸_F) K = G(𝔸_F)` with the
  parabolic factor on the left.

Maximality of `K` is not required. `IsParabolicIwasawaCompact.isIwasawaCompact` derives the
structure from the published `IsParabolicIwasawaCompact F G P p K`, which also asks that `K` be
maximal compact. `IsIwasawaCompact.of_comp` passes from a subgroup `f : P₀ ⟶ P` to `P`. If
`P₀(𝔸_F) K = G(𝔸_F)` for the minimal parabolic `P₀`, the same `K` is an Iwasawa subgroup for
every parabolic containing it, as in MW I.1.4 (i). The helper `map_comp_apply_of_hom` records
`map (f ≫ p) x = map p (map f x)`.

## The height

`IsIwasawaCompact.exists_eq` writes every `g` as `g = p(q) k` with `q ∈ P(𝔸_F)` and `k ∈ K`.
For `hK : IsIwasawaCompact p K`, the height `hK.height g` is `characterLog F P q` for the
factorization chosen there.

The results are, for `hK : IsIwasawaCompact p K`:

- `characterLog_eq_zero_of_map_mem`: if `K` is compact and `p(q) ∈ K`, then
  `characterLog F P q = 0`.
- `IsIwasawaCompact.characterLog_eq`: two factorizations `p(q) k = p(q') k'` with `k, k' ∈ K`
  have `characterLog F P q = characterLog F P q'`.
- `IsIwasawaCompact.height_eq`: the height is computed by *any* factorization `g = p(q) k`,
  `k ∈ K`.
- `IsIwasawaCompact.height_mul_right`: `H_P(g k) = H_P(g)` for `k ∈ K`.
- `IsIwasawaCompact.height_map_mul`: `H_P(p(q) g) = log_P(q) + H_P(g)` for `q ∈ P(𝔸_F)`.
- `IsIwasawaCompact.height_map`: `H_P(p(q)) = log_P(q)`.
- `IsIwasawaCompact.height_rational_mul`: `H_P(p(γ) g) = H_P(g)` for a principal point `γ` of
  `P(F)`.
- `IsIwasawaCompact.height_of_mem`: `H_P(k) = 0` for `k ∈ K`.

The height depends on `K`. Two Iwasawa subgroups give heights that differ in general, and the
module claims no independence.

## Levi form

For a group scheme `U` over `F`, `GroupScheme.IsUnipotent U` is the published unipotence
predicate.

- `characterLog_eq_zero_of_isUnipotent`: a unipotent `U` has zero logarithmic functional,
  because its only rational character is zero (published
  `IsUnipotent.rationalCharacter_eq_zero`).
- `IsIwasawaCompact.height_unipotent_mul`: for a homomorphism `iU : U ⟶ P` from a unipotent `U`,
  `H_P(p(iU(x)) g) = H_P(g)`.
- `IsIwasawaCompact.height_eq_levi`: for unipotent `iU : U ⟶ P`, any `l : M ⟶ P`, `u ∈ U(𝔸_F)`,
  `m ∈ M(𝔸_F)` and `k ∈ K`,
  `H_P(p(iU(u) · l(m)) k) = realCharacterDualMap F M P l (log_M(m))`.
- `realCharacterDualMap_comp_apply` and `realCharacterDualMap_id_apply`: the covariant maps of
  real character duals are functorial.
- `IsIwasawaCompact.realCharacterDualMap_height_eq`: if moreover `q : P ⟶ M` satisfies
  `l ≫ q = 𝟙 M` (a Levi projection), then
  `realCharacterDualMap F P M q (H_P(p(iU(u) · l(m)) k)) = log_M(m)`.

For a parabolic `P = M U` with Levi `M`, unipotent radical `U` and Levi projection `q`, the last
result is MW's `log_M(m_P(g))` for `g = u m k`. The module does not prove that `P(𝔸_F)` is the
product `U(𝔸_F) M(𝔸_F)`, nor that `realCharacterDualMap F M P l` is bijective. Both are
needed to turn the formula into the statement that the two heights determine each other for
every `g`. The formula is stated for points already written as `u m k`.

## Proofs

**`characterLog_eq_zero_of_map_mem`.** The published `isClosedEmbedding_map` makes
`map F P G p` a closed embedding, so the preimage of the compact `K` is a compact subgroup of
`P(𝔸_F)`. The published `characterLog_eq_zero_on_compactSubgroup` applies.

**`characterLog_eq`.** From `p(q) k = p(q') k'`, the point `p(q'⁻¹ q) = k' k⁻¹` lies in `K`. So
`characterLog F P (q'⁻¹ q) = 0`, and `q = q' (q'⁻¹ q)` with the published `characterLog_mul`
gives the claim.

**`height_eq`, `height_mul_right`, `height_map_mul`, `height_map`, `height_rational_mul`,
`height_of_mem`.** Each compares the chosen factorization with an explicit one through
`characterLog_eq`. For `height_mul_right` the explicit factorization is `p(q) (k₀ k)`, and for
`height_map_mul` it is `p(q q₀) k₀`. `height_rational_mul` uses the published
`characterLog_rational` (product formula).

**`characterLog_eq_zero_of_isUnipotent`.** Evaluate at a character `χ`. It is zero, and the
logarithm of the norm of the zero character is `log 1 = 0` (published `characterNorm_zero`).

**`height_unipotent_mul` and `height_eq_levi`.** `height_map_mul` and the published
`characterLog_map` reduce the first to `characterLog_eq_zero_of_isUnipotent`. The second
follows from the first, `characterLog_map` and `height_eq`.

**Functoriality and `realCharacterDualMap_height_eq`.** The covariant map is precomposition with
the published `characterRestrict`, so its functoriality is that of `characterRestrict_comp` and
`characterRestrict_id`. With `l ≫ q = 𝟙`, the composite of the two covariant maps is the identity.

**`of_comp`.** The range of `map (f ≫ p)` lies in the range of `map p`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series*, Cambridge
  University Press, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`
  (folder SHA-256 `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`). Chapter
  file `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, I.1.4: `Re a_M = Hom_Z(Rat(M), ℝ)`,
  printed p. 5 (PDF p. 5); `log_M` by equation (4) and the map `m_P : G → M¹ \ M`,
  `m_P(umk) = M¹ m`, well defined because `M ∩ K ⊆ M¹`, printed p. 7 (PDF p. 7). I.1.4 (i), printed
  p. 4 (PDF p. 4): `G(𝔸) = P₀(𝔸) K`.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, 2024, registered as
  `getz-hahn-2024-automorphic-representations` (SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), §2.7, Theorem 2.7.1,
  printed p. 71 (PDF p. 88): `G(𝔸_F) = P(𝔸_F) K` for a maximal compact `K`. The October 2026
  author errata have no Chapter 2 entry.

The module generalizes MW's construction in one respect: `P` is any closed subgroup with a
compact `K` satisfying `P(𝔸_F) K = G(𝔸_F)`, and the height takes values in `Hom_Z(Rat(P), ℝ)`
before passing to a Levi. MW's well-definedness argument (`M ∩ K ⊆ M¹`) appears here as
`characterLog_eq_zero_of_map_mem`.
