# Rapid decay of Levi cusp forms on norm-one representatives

Module `Langlands.Global.AdelicLeviCuspFormRapidDecayStatement` states the proposition
`Langlands.Global.LeviCuspFormRapidDecayStatement`. It does not prove it.

## Statement

Let `F` be a number field, `G` an affine group over `F` with a compatible standard parabolic family
`fam` (`StandardParabolicFamily`, module `Langlands.Global.AdelicLeadingCuspidalComponents`), and
`K` a subgroup of `G(𝔸)` such that

- `K` is a maximal compact subgroup of `G(𝔸)` (`IsMaximalCompactSubgroup`);
- the minimal standard parabolic `P₀`, the member of the family with empty Levi simple-root set,
  satisfies `P₀(𝔸)K = G(𝔸)` (`IsIwasawaCompact`);
- for every standard index `J` the inverse image of `K` in `M_J(𝔸)` is a maximal compact subgroup
  of `M_J(𝔸)`.

Let `rho : G → GL_N` be a closed matrix embedding (`IsClosedSubgroup rho`) with `N > 0`, `H` the
Library's adelic matrix height `adelicHeight F G rho` on `G(𝔸)`, and `Kinf` the inverse image of
`K` in `G(F_∞)`.

Let `J` be a standard index, `ι : M_J(𝔸) → G(𝔸)` the map induced by the Levi inclusion
`fam.l J ≫ fam.p J`, and `ψ` a cusp form on `M_J(F) \ M_J(𝔸)`, that is
`fam.IsLeviCuspForm Kinf rho J ψ`: an automorphic form for the rational subgroup of `M_J`, the group
`K_∞ ∩ M_J(F_∞)` and the embedding `ι ≫ rho`, whose constant terms along all proper parabolic
subgroups of `M_J` vanish.

The proposition asserts: for every real `e ≥ 0` there is a constant `B ≥ 0` such that every class
`x` of the norm-one rational quotient `M_J(F) \ M_J(𝔸)^1` (`NormOneRationalQuotient`) has a
representative `m ∈ M_J(𝔸)^1` with

`H(ι m)^e · |ψ(m)| ≤ B`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`:
  - I.2.1, printed pp. 18–20: Siegel domains `𝔖` with `G = G(k)𝔖` (number field case);
  - I.2.2, printed pp. 20–24: the height `‖g‖` and its comparison properties, in particular
    (vi) on `G^c ∩ 𝔖`;
  - I.2.12, printed pp. 34–35: rapidly decreasing functions on `𝔖`
    (`|φ(ag)| ≤ c ‖a‖^r m_{P₀}(g)^λ` for every `λ`, `a ∈ A_G`, `g ∈ G^1 ∩ 𝔖`) and the Corollary
    that `sφ` is rapidly decreasing for smooth `K`-finite `φ` whose derivatives have uniformly
    moderate growth;
  - I.2.17, printed pp. 37–39: automorphic forms and the uniform moderate growth of their
    derivatives;
  - I.2.18, printed p. 39: a cuspidal automorphic form is rapidly decreasing (`sφ = φ` since all
    proper constant terms vanish).
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`:
  §6.2, p. 202, (6.8) and the following display: the pairing `(φ(· g), ψ)_{𝔛_M^1}` against
  cusp forms `ψ` on `M(F) \ M(𝔸)`, integrated over the norm-one quotient
  `𝔛_M^1 = M(F) \ M(𝔸)^1`, whenever the integral converges absolutely. (The phrase
  "necessarily rapidly decreasing" just before (6.7) refers to the tests `(f ∘ H_P) ψ'` on the
  parabolic quotient with `f` smooth and compactly supported, not to cusp forms on the full Levi
  quotient: for a split torus the constant function is cuspidal and the height is unbounded on
  the full quotient. The proposition here concerns only the norm-one quotient.)

## Correspondence with the sources

- Apply MW I.2.18 and the Corollary of I.2.12 to the reductive group `M_J` and its cusp form `ψ`.
  On the norm-one part of a Siegel domain of `M_J` the central factor is trivial, and rapid decrease
  bounds `|ψ(m)|` by every power `m_{P₀}(m)^λ`. By MW I.2.1 every class of `M_J(F) \ M_J(𝔸)^1` has
  a representative in this part of the Siegel domain (a rational translate of a norm-one point is
  norm one by the product formula). On the norm-one part `M_J^1 ∩ 𝔖` of the Siegel domain one has
  `H(ι m) ≤ C m_{P₀^M}(m)^{λ₀}` for a fixed `λ₀` (MW I.2.2 (vi), applied with `G^c = G^1` as chosen
  in I.2.1 over a number field); the restriction to the norm-one part is essential. Taking the
  decay exponent `-e λ₀` in I.2.12 gives the stated bound after absorbing `C^e`. This derivation is
  explanatory and is not formalized here.
- The statement measures size by the height of the ambient group `G` through `ι`, which is the
  weight used in the Library's norm-one Levi pairing estimates
  (`WeightedLeviPairingIntegrabilityStatement`, module
  `Langlands.Global.AdelicWeightedLeviPairing`). The representatives are those of the Library's
  quotient `NormOneRationalQuotient`; the bound is required at one representative of each class.
- The compact subgroup satisfies the hypotheses used throughout the standard-family statements of
  the Library (for example `CuspidalProjectionDecompositionStatement`): MW work with a maximal
  compact subgroup in good position, and the cusp form is finite under `K_∞ ∩ M_J(F_∞)`.
