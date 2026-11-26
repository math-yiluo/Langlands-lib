# Smoothness of the Iwasawa height in the infinite variable

Module `Langlands.Global.AdelicIwasawaSmoothHeightStatement` contains one `Prop`-valued
definition, `Langlands.Global.IwasawaSmoothHeightPairingsStatement`, and no theorems. It states
the statement; the module does not prove it.

## The statement

`IwasawaSmoothHeightPairingsStatement.{u}` quantifies over

- a number field `F : Type u`;
- group schemes `G` and `P` over `Spec F`, with `G` affine;
- a homomorphism `p : P ⟶ G`;
- a subgroup `K` of the actual adelic points `AdelicGroupPoints F G` and a proof
  `hK : IsIwasawaCompact p K`, i.e. `K` is compact and `P(𝔸) K = G(𝔸)` (literal covering
  `Set.range (map F P G p) * K = Set.univ`, parabolic factor on the left);
- a natural number `d` and `hsmooth : SmoothOfRelativeDimension d G.X.hom`, which fixes the
  Library's charted space and Lie group structure on the infinite adelic points.

Under the hypotheses `IsConnectedReductive G`, `IsParabolicSubgroup p` and
`IsMaximalCompactSubgroup F G K`, it asserts `hK.HasSmoothHeightPairings hsmooth`. By the
definition of `IsIwasawaCompact.HasSmoothHeightPairings` (module
`Langlands.Global.AdelicEisensteinDifferentialParameters`) this means: for every complex
character parameter `λ : ComplexCharacterParameter F P` and every finite adelic point `b`, the
function

```
a ↦ complexParameterPairing F P λ (hK.height (pair F G a b))
```

on `InfiniteAdelicGroupPoints F G` is `ContMDiff` of order `∞` from the model
`𝓘(ℝ, smoothModel F d)` to `𝓘(ℝ, ℂ)`. Here `hK.height` is the Iwasawa height `H_P` of
`Langlands.Global.AdelicIwasawaHeight`: for `g = p(q) k` with `k ∈ K` it is the logarithmic
functional `log_P(q) ∈ Hom(Rat(P), ℝ)`. Since `m_P(g)^λ = exp ⟨λ, H_P(g)⟩` is
`hK.heightPower λ g`, the statement says that `g ↦ m_P(g)^λ` has smooth infinite slices.

The parabolic need not be standard for a chosen minimal parabolic, and `K` is only assumed
maximal compact with `P(𝔸) K = G(𝔸)`; no compatibility with Levi subgroups is required.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234, registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2, p. 191 (TeX `1911.02342.tex`,
  lines 403–423). They define `m_P : G(𝔸) → M(𝔸)/M(𝔸)^1` as the left `U(𝔸)`-invariant,
  right `K`-invariant extension of the projection, set `φ_λ(g) = φ(g) m_P(g)^λ` for an
  automorphic form `φ` on `U(𝔸)M(F) \ G(𝔸)`, and state "We have `φ_λ ∈ 𝒜_P`". Automorphic forms
  are smooth (Mœglin–Waldspurger I.2.17 (ii)); for the constant form `φ = 1` this is the
  smoothness of `m_P^λ`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`, I.1.4,
  printed pp. 6–7 (chapter PDF `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, PDF pp. 6–7):
  `log_M` by `⟨χ, log_M(m)⟩ = log |m^χ|` and the map `m_P` defined through `G = PK`.

## Provenance

The statement is derived. The sources take a maximal compact subgroup `K = ∏_v K_v` in good
position for a fixed minimal parabolic and a standard parabolic `P`. Here `K` is any maximal
compact subgroup of `G(𝔸)` with `P(𝔸) K = G(𝔸)`. Smoothness only concerns the infinite variable:
a maximal compact subgroup of `G(𝔸)` is the product of maximal compact subgroups of the infinite
and finite adelic points (module `Langlands.Global.AdelicMaximalCompactFactors`), so at a fixed
finite point the height is the height of the infinite component up to an additive constant.
The statement uses the pairing `⟨λ, H_P⟩` rather than `m_P^λ = exp ⟨λ, H_P⟩`. The two
formulations are equivalent: the exponential of a smooth function is smooth, and for real `λ`
the pairing is the logarithm of the positive function `m_P^λ`; the pairing is complex linear in
`λ`.
