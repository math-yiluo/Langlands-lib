# Square-integrable automorphic forms on `A_M U(𝔸) M(F) \ G(𝔸)`

Module `Langlands.Global.AdelicSquareIntegrableInducedForms` defines Lapid's
spaces `A^n_P` and `A^2_P` as predicates on functions on `G(𝔸)`, the
parameters `2ρ_P` and `ρ_P`, and the real-linear map whose image is the
space `i𝔞_P^*` of imaginary parameters. It is a definition module and proves
nothing.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
page = printed page + 9).

- §2, p.311: `A_P` is the space of automorphic forms on `U(𝔸)P \ G(𝔸)`.
  `A^n_P` is the subspace of `φ ∈ A_P` with `φ(ag) = δ_P(a)^{1/2} φ(g)` for
  all `a ∈ A_M`. `A^2_P` is the subspace of `φ ∈ A^n_P` with
  `‖φ‖²_P = ∫_{A_M P U(𝔸) \ G(𝔸)} |φ(g)|² dg < ∞`. Lapid uses Arthur's
  conventions [Art80], in particular `M(𝔸) = M(𝔸)^1 × A_M`, and chooses Haar
  measures on `G(𝔸)`, `M(𝔸)`, `U(𝔸)`, `K` and `𝔞_P` compatibly with the
  Iwasawa decomposition.
- §2–§3, pp.311–314: parameters `λ ∈ 𝔞^*_{P,ℂ}`, and the imaginary
  parameters `λ ∈ i𝔞_P^*` over which wave packets are integrated.

Mœglin–Waldspurger I.1.13 (registered as
`moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, printed p.18) fixes
`meas(K) = 1` and `meas(U(F) \ U(𝔸)) = 1`, and gives the compatibility
formula `∫_G f(g) dg = ∫_{U(𝔸) × M × K} f(umk) m^{-2ρ_P} dk dm du`.

## Existing objects used

- `RealCharacterParameter F P = ℝ ⊗[ℤ] X^*(P)`,
  `ComplexCharacterParameter F P = ℂ ⊗[ℤ] X^*(P)` and
  `parameterPower F P λ m = exp ⟨λ, log_P(m)⟩` (module
  `Langlands.Global.AdelicComplexParameters`). Here `log_P(m)` is
  `characterLog F P m`, whose value at `χ` is `log |χ(m)|_𝔸`. So
  `parameterPower F P (s ⊗ χ) m = |χ(m)|_𝔸^s`.
- `Lie.adjointDeterminantCharacter P`, the rational character
  `det(Ad | Lie P)` of `P` (module
  `Langlands.GroupScheme.Lie.AdjointDeterminantCharacter`).
- `RestrictionSplitCentre.canonicalSubgroup F M`, `CanonicalQuotient F M` and
  `canonicalMeasure F M` (module
  `Langlands.Global.AdelicRestrictionSplitCentreCanonical`): the subgroup
  `A_M` of `M(𝔸)`, the quotient `[M] = A_M M(F) \ M(𝔸)` and a measure on it.
  `A_M` is the image of the positive real points of a chosen split component
  of `Res_{F/ℚ} M`. These need `F : Type`, so the second section of this
  module is stated in universe `0`.
- `compactHaarProbability F G K hK` (module
  `Langlands.Global.AdelicParabolicModulus`), the Haar probability measure on
  a compact subgroup `K` of `G(𝔸)`.
- `parabolicQuotientSubgroup F p iU l`, the subgroup `U(𝔸)M(F)` of `G(𝔸)`
  (module `Langlands.Global.AdelicParabolicQuotient`), and
  `IsAutomorphicFunctionOn` (module
  `Langlands.Automorphic.GroupSchemeInvariantForms`): left invariance,
  smoothness, finiteness under the archimedean compact subgroup,
  `𝔷`-finiteness and moderate growth (Mœglin–Waldspurger I.2.17).

## Definitions

Namespace `Langlands.Global.AdelicGroupPoints`.

- `imaginaryParameter F P : X^*(P) ⊗ ℝ →ₗ[ℝ] X^*(P) ⊗ ℂ` sends `r ⊗ χ` to
  `(r i) ⊗ χ`. Its range is `i𝔞_P^*` inside `𝔞^*_{P,ℂ} = 𝔞_P^* ⊗ ℂ`.
- `modulusParameter F P = 1 ⊗ det(Ad | Lie P)`, the parameter `2ρ_P`, and
  `halfModulusParameter F P = ½ ⊗ det(Ad | Lie P)`, the parameter `ρ_P`. They
  need `P` affine and locally of finite type.

For `G`, `P`, `M`, `U` affine and locally of finite type over a number field
`F : Type`, `p : P ⟶ G`, `iU : U ⟶ P`, `l : M ⟶ P` and `φ : G(𝔸) → ℂ`:

- `IsSplitComponentEquivariant p l φ`: for every `a ∈ A_M` and `g ∈ G(𝔸)`,
  `φ(l(a) g) = a^{ρ_P} φ(g)` (with `l(a)` mapped into `G(𝔸)` by `p`). This
  is Lapid's condition defining `A^n_P` inside `A_P`.
- `IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ`, for a
  compact subgroup `K` of `G(𝔸)`, is the conjunction of
  1. `φ ∈ A_P`: `IsAutomorphicFunctionOn` for the subgroup `U(𝔸)M(F)`, the
     archimedean part `K.comap (ofInfinite F G)` of `K` and the matrix
     representation `rho`;
  2. `IsSplitComponentEquivariant p l φ`;
  3. integrability of `(k, x) ↦ |m^{-2ρ_P}| · |φ(m k)|²`, with `m` the chosen
     representative `x.out ∈ M(𝔸)` of `x ∈ [M]`, on `K × [M]` for the product
     of `compactHaarProbability F G K hKc` and `canonicalMeasure F M`.

  This is Lapid's `A^2_P`.

## Correspondence with the source

- `ρ_P`. For `m ∈ P(𝔸)`, `m^{2ρ_P} = |det(Ad(m) | Lie P)|_𝔸`. The modulus
  `δ_P(m)`, the factor by which conjugation by `m` scales Haar measure on
  `U(𝔸)`, equals this. The published (unproved) statements
  `AdelicModularCharacterAdjointDeterminantStatement` (the modular character
  of `P(𝔸)` is `|det(Ad | Lie P)|_𝔸`) and `AdelicParabolicModulusStatement`
  (for a parabolic `P = P(χ)` this modular character is `δ_P`, which is also
  `|det(Ad | Lie U)|_𝔸`) together give `m^{2ρ_P} = δ_P(m)`. Algebraically,
  `det(Ad | Lie P) = det(Ad | Lie U)` as characters of `P`, because
  `det ∘ Ad` of the connected reductive Levi quotient is trivial. This is
  explanatory and not used by the definitions. Since `m^{ρ_P}` is a positive
  real number with square `m^{2ρ_P}`, it is the source's `δ_P(m)^{1/2}`.
- `A_M`. Arthur and Lapid write `M(𝔸) = M(𝔸)^1 × A_M`, where `A_M` is the
  identity component of the real points of the split component of the centre
  of `Res_{F/ℚ} M`; Getz–Hahn (2.20) use the same group. A split component of
  `Res_{F/ℚ} M` in the sense of the published `IsSplitComponent` is a central
  split torus that admits no proper factorization through another central
  split torus, that is, the largest central `ℚ`-split torus. So
  `canonicalSubgroup F M` is the source's `A_M`. The published module notes
  that it does not prove the agreement with Getz–Hahn's description. This is
  explanatory and not proved here.
- `A_P`. Lapid's `U(𝔸)P \ G(𝔸)` is `U(𝔸)M(F) \ G(𝔸)`, since
  `P(F) = M(F)U(F)` and `U(F) ⊆ U(𝔸)`. The automorphy conditions are those of
  Mœglin–Waldspurger I.2.17, as for `𝒜_P` in the Bernstein–Lapid
  statements (for example `EisensteinAbsoluteConvergenceStatement`).
- The `L²` condition. The function `|φ|²` is left invariant under
  `U(𝔸)M(F)` and satisfies `|φ(ag)|² = δ_P(a)|φ(g)|²` for `a ∈ A_M`, so
  Lapid's integral over `A_M P U(𝔸) \ G(𝔸)` is the integral of a
  `δ_P`-equivariant function. With `G(𝔸) = U(𝔸) M(𝔸) K`,
  `meas(U(F) \ U(𝔸)) = 1` and MW's compatibility formula, it equals
  `∫_K ∫_{[M]} δ_P(m)⁻¹ |φ(m k)|² dm dk`. The integrand on `K × M(𝔸)` is
  left `M(F)`-invariant (`φ` is, and `δ_P` is trivial on `M(F)` by the
  product formula) and left `A_M`-invariant (by the `A^n_P` condition), so it
  does not depend on the representative `x.out`. Finiteness does not depend
  on positive constant multiples of the measures; in particular the
  normalization of `canonicalMeasure F M` (a pushforward of Haar measure on
  the norm-one subgroup, not MW's normalization) is irrelevant. These facts
  are explanatory and not proved here.
- The compact subgroup. Lapid fixes `K` in good position with respect to a
  minimal Levi. Here `K` is any compact subgroup of `G(𝔸)`; statements that
  use these predicates add `P(𝔸)K = G(𝔸)` and maximality. For such `K` the
  integral above is Lapid's integral, which does not involve `K`.
- `i𝔞_P^*`. `𝔞_P^* = X^*(P) ⊗ ℝ` and `𝔞^*_{P,ℂ} = X^*(P) ⊗ ℂ`, as in the
  Library's `ComplexCharacterParameter` (Bernstein–Lapid §2.1 use
  `X^*(M)`, equal to `X^*(P)` by restriction). The pairing with
  `H ∈ Hom(X^*(P), ℝ)` sends `imaginaryParameter F P μ` to `i⟨μ, H⟩`.

## Scope

Lapid's inner product `(·,·)_P`, the realization of `A^2_P` as a dense
subspace of `Ind L²_disc(A_M M \ M(𝔸))`, the measures on `𝔞_P` and
`i𝔞_P^*`, and the space `W_P` of wave packets are not defined here. The
definitions take arbitrary `p`, `iU`, `l` and `K`: that `P` is parabolic,
`U` its unipotent radical, `M` a Levi, and `K` maximal compact with
`P(𝔸)K = G(𝔸)` are hypotheses of the statements that use them.
