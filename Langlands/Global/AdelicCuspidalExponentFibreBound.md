# Forms with only negative maximal cuspidal exponents on the fibres of `H_{P_R}`

Module `Langlands.Global.AdelicCuspidalExponentFibreBound`. It states and proves
`Langlands.Global.StandardParabolicFamily.CuspidalExponentFibreBoundStatement` (theorem
`cuspidalExponentFibreBound`). Under the hypotheses of `CuspidalExponentRegionBoundStatement`
(module `Langlands.Global.AdelicCuspidalExponentRegionBound`), the automorphic function `f` on
`U_R(𝔸) M_R(F) \ G(𝔸)` is bounded on every fibre of the Iwasawa height
`H_{P_R} : G(𝔸) → Hom(X^*(P_R), ℝ)`. This is a step towards the boundedness on `M_R(𝔸)^1`
that Bernstein–Lapid use in §6.4.

## Relative reduction theory (`exists_relativeSiegelCover`)

Let `K` be a compact subgroup with `P_0(𝔸) K = G(𝔸)` and `R` a standard index. There are a
compact set `Ω` and a real number `t > 0` with these properties. `Ω` is contained in the image of
`P_0(𝔸)`, and every point of `Ω` is the image of a point of `P_R(𝔸)` with zero logarithm
(`characterLog`). Every `x ∈ G(𝔸)` satisfies `p a k = γ x` for some `γ ∈ P_R(F)`, `p ∈ Ω`, a
positive torus point `a` with `|α(a)|_𝔸 ≥ t` for the simple roots `α` of `R`, and `k ∈ K`.

The proof is the argument of the published `iwasawaSiegelCovering` (module
`Langlands.Global.ArthurSiegelCoveringProof`) for the parabolic `P_1 = P_R`, written for the
members of the family. The published `exists_relativeChamberReduction` gives `q ∈ P_R(F)` with
`q x = n m a k`, where `n ∈ N_0(𝔸)`, `m ∈ M_0(𝔸)^1`, the torus point `a` is in the chamber of
the roots of `R` and `k ∈ K`. The compact covers `Ω_M` of `M_0(F) \ M_0(𝔸)^1` (published
`exists_leviCompactCover_of_setup` with `centralSplitCompactQuotient`) and `Ω_N` of
`N_0(F) \ N_0(𝔸)` (published `exists_unipotentCompactCover_of_setup`) move `m` and then `n` into
compact sets. The rational points used lie in `P_0(F) ⊆ P_R(F)`. The set `Ω` is the image of
`Ω_N × Ω_M`. The standard unipotent radical `N_0` and the standard Levi `M_0` lie in `P_R`, and
`SubgroupFunctor.rangeFactor` factors them through `P_R`. A point of `N_0(𝔸)` has zero
logarithm because `N_0` is unipotent, and a point of `M_0(𝔸)^1` has zero logarithm by the
definition of the norm-one subgroup.

## Real forms annihilated by the coroots of `R`

- `span_roots_sup_corootAnnihilator`: the real span of the simple roots of `R` and
  `corootAnnihilator R` together span `𝔞_0^*`. The published `StandardLevi.complements` shows
  that they are complementary, using a Weyl-invariant inner product (published
  `ArthurRelative.exists_isWeylInvariantInnerProduct`).
- `exists_parabolicParameter_of_mem_corootAnnihilator`: every `φ ∈ corootAnnihilator R` is the
  restriction to the torus, along `T → M_R → P_R`, of a real character parameter `m` of `P_R`.
  The published `standardLeviCharacterAnnihilator` identifies `corootAnnihilator R` with the
  restrictions of the real characters of `M_R`. Restriction of characters from `P_R` to its
  rational Levi `M_R` is bijective (published `IsRationalLeviSubgroup.characterRestrict_bijective`),
  hence surjective after `ℝ ⊗ −`.
- `realParameterPairing_cocharacterFunctional`: the pairing of a real character of the torus with
  the functional `cocharacterFunctional H` of `H ∈ 𝔞_0` is `pair φ H`.
- `realParameterPairing_height_mul`: let `p` be the image of a point of `P_R(𝔸)` with zero
  logarithm, `a` a positive torus point with logarithm `H` and `k ∈ K`. Then
  `⟨m, H_{P_R}(p a k)⟩ = φ(H)`, where `φ` is the restriction of `m` to the torus. The Iwasawa
  height is right `K`-invariant and adds the logarithm of a left `P_R(𝔸)` factor (published
  `IsIwasawaCompact.height_mul_right` and `height_map_mul`). The torus point is the image of
  `T → P_R`, and `characterLog` is natural (`characterLog_map`).

## The statement

`CuspidalExponentFibreBoundStatement 𝓕 hG rho` assumes `N > 0` and that `rho` is a closed
embedding. Let `K` be a subgroup with `P_0(𝔸) K = G(𝔸)` (`IsIwasawaCompact`, which includes
compactness). Let `Kinf` be a maximal compact subgroup of `G(F_∞)`, `R` a standard index with
`P_R(𝔸) K = G(𝔸)`, and `f` an automorphic function on `U_R(𝔸) M_R(F) \ G(𝔸)`. Assume the
exponent decompositions of the constant terms `C_{R \ {α}} f`, `α ∈ R`, with their negativity
condition, exactly as in `CuspidalExponentRegionBoundStatement`. Then for every `x₀ ∈ G(𝔸)` there
is `C` with `|f(x)| ≤ C` whenever `H_{P_R}(x) = H_{P_R}(x₀)`.

## The proof (`cuspidalExponentFibreBound`)

Let `Ω` and `t` be as in `exists_relativeSiegelCover`. Choose a basis `φ_1, …, φ_r` of
`corootAnnihilator R` and parameters `m_j` of `P_R` restricting to `φ_j`, and put
`B = ∑_j |⟨m_j, H_{P_R}(x₀)⟩|` and `Φ = {φ_1, …, φ_r}`. Then `Φ` and the simple roots of `R` span
`𝔞_0^*`. Let `Y_f` be the product of the finite parts of `Ω` and of `K`, which is compact. By
`cuspidalExponentRegionBound` there is `C` bounding `f` on the points `p a k` with `p ∈ Ω`,
`|α(a)|_𝔸 ≥ t` for `α ∈ R`, `|φ_j(log a)| ≤ B`, `k ∈ K` and finite part in `Y_f`.

Let `x` lie in the fibre of `x₀` and write `p a k = γ x`. Then `f(x) = f(p a k)`, since `f` is
left invariant under `P_R(F)` (published `rationalImage_le_parabolicQuotientSubgroup_of_le`). The
height is invariant under `P_R(F)` (published `IsIwasawaCompact.height_rational_mul`), so
`H_{P_R}(p a k) = H_{P_R}(x₀)`. Hence `φ_j(log a) = ⟨m_j, H_{P_R}(x₀)⟩` by
`realParameterPairing_height_mul`, and `|φ_j(log a)| ≤ B`. The finite part of `a` is trivial, so
the finite part of `p a k` lies in `Y_f`. Therefore `|f(x)| ≤ C`.

## Sources and provenance

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.1 (pp. 18–20), Siegel
  domains `S = {p a k}` and `G(𝔸) = G(F) S`.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series* (2024),
  registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: §6.4 (p. 204), where
  the boundedness of right translates on `G(𝔸)^1` is deduced from Mœglin–Waldspurger I.4.1.

The statement is derived. It passes from the bound on Siegel regions of `M_R` to the fibres of
`H_{P_R}`, a step that Bernstein–Lapid leave implicit. The relative reduction theory follows the
proof of the published `iwasawaSiegelCovering` for the parabolic `P_R`.
