# Finite changes of the Iwasawa compact in `A^2_P` and in the Levi pairings (3.7)

Module `Langlands.Global.AdelicFiniteCompactPairingComparisonStatement` states one proposition,
`Langlands.Global.FiniteCompactPairingComparisonStatement`. It proves nothing.

The proposition compares two maximal compact subgroups `K₁`, `K₂` of `G(𝔸)` that satisfy the
Iwasawa decomposition for a standard parabolic `P` and have the same infinite projection. It
compares them in two places: Lapid's space `A^2_P` of square-integrable inducing forms, and the
pairings `(φ, ψ)^X_P` of Delorme 2023, (3.7), with the Library's normalized measures. Its use is
to transfer statements about (3.7) proved for one compact, for example a compact in good
position, to every maximal Iwasawa compact with the same infinite projection. That includes the
compacts that are not conjugate to one in good position.

## Statement

The data: a number field `F : Type`; a group `G` over `F` with `[IsAffineHom G.X.hom]`,
`[IsAffine G.X.left]`, `[LocallyOfFiniteType G.X.hom]`; a compatible family
`𝓕 : StandardParabolicFamily F G` of standard parabolics (it contains
`IsConnectedReductive G`); a standard index `J`, with `P = 𝓕.P J`, `M = 𝓕.M J`, `U = 𝓕.U J`
and the instance `[IsClosedImmersion (𝓕.p J).hom.hom.left]` that the Iwasawa height needs (it
holds for every member of the family by `(𝓕.isCompatible J).parabolic.isClosedSubgroup`). Then
come two subgroups `K₁`, `K₂` of `G(𝔸)` with

- `hK₁ : IsIwasawaCompact (𝓕.p J) K₁` and `hK₂ : IsIwasawaCompact (𝓕.p J) K₂`: each `K_i` is
  compact and `P(𝔸) K_i = G(𝔸)`;
- `IsMaximalCompactSubgroup F G K₁` and `IsMaximalCompactSubgroup F G K₂`;
- `K₁.map (infinite F G) = K₂.map (infinite F G)`: the same image in `G(𝔸_∞)`.

The statement names four objects with `let`:

- `Δ g = hK₁.height g - hK₂.height g ∈ RealCharacterDual F P = 𝔞_P`, the difference
  `H_P^{K₁}(g) - H_P^{K₂}(g)` of the two Iwasawa heights (`IsIwasawaCompact.height`: for
  `g = p(q) k` with `k ∈ K`, `H_P^K(g) = log_P(q)`);
- `cut v φ = {g | Δ g = v}.indicator φ`, that is `φ_v = 1_{Δ = v} φ`;
- `Γ = parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J)`, the subgroup `U(𝔸) M(F)` of
  `G(𝔸)`;
- `δinv = parameterPower F P (-modulusParameter F P)`, `x ↦ x^{-2ρ_P} = δ_P(x)⁻¹` on `P(𝔸)`.

The conclusion is the conjunction of four assertions.

1. **Finite partition.** There is a finite set `S ⊂ 𝔞_P` with `Δ g ∈ S` for every `g`.
2. **Clopen fibres.** Every fibre `{g | Δ g = v}` is clopen in `G(𝔸)`.
3. **Inducing forms.** For all `N`, `d`, `rho`, `hsmooth`, `hcalc` and every `φ` with
   `IsSquareIntegrableInducedForm K₁ hK₁.isCompact rho hsmooth hcalc (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ`
   (Lapid's `A^2_P` for `K₁`), and every `v ∈ 𝔞_P`, `cut v φ` satisfies
   `IsSquareIntegrableInducedForm K₂ hK₂.isCompact rho hsmooth hcalc (𝓕.p J) (𝓕.iU J) (𝓕.l J)`
   with the same matrix representation `rho` and the same smoothness data `hsmooth`, `hcalc`.
4. **Levi pairings.** There is a real `c > 0` such that for all `φ`, `ψ : G(𝔸) → ℂ` that are
   continuous and left invariant under `Γ` (`IsLeftInvariantUnder F G Γ`), every `v ∈ 𝔞_P` and
   all `x`, `x' ∈ 𝓕.positiveSplitComponent J` (`𝔄_P`) with
   `characterLog F P x' = characterLog F P x - v` (that is `H_P(x') = H_P(x) - v`):
   - `𝓕.squareIntegrablePairingIntegrand K₁ J x (cut v φ) ψ` is integrable for
     `𝓕.squareIntegrablePairingMeasure K₁ hK₁.isCompact J` if and only if
     `𝓕.squareIntegrablePairingIntegrand K₂ J x' (cut v φ) ψ` is integrable for
     `𝓕.squareIntegrablePairingMeasure K₂ hK₂.isCompact J`;
   - `δinv x * ∫ (K₁-integrand at x) = c * (δinv x' * ∫ (K₂-integrand at x'))`, the integrals
     being taken for the same two measures.

   The constant `c` is chosen before `φ`, `ψ`, `v`, `x` and `x'`: it depends only on `𝓕`, `J`,
   `K₁` and `K₂`.

For a first entry `θ`, a second entry `ψ` and `x ∈ P(𝔸)`, the pairing integrand
`𝓕.squareIntegrablePairingIntegrand K J x θ ψ` (module
`Langlands.Global.AdelicTemperedVanishingReduction`) is the function
`(k, m) ↦ θ(x m k) · conj ψ(x m k)` on `K × M(F) \ M(𝔸)^1` (`NormOneRationalQuotient F M`),
evaluated at the representative `m = Quotient.out` in `M(𝔸)^1`. The pairing measure is
`compactHaarProbability F G K hKc` times `normOneRationalQuotientHaarMeasure F M`, the Haar
probability of `K` times the Library's fixed quotient of a Haar measure of `M(𝔸)^1` by `M(F)`.
Both sides of assertion 4 use the same measure on `M(F) \ M(𝔸)^1`. Only the compact changes:
from `K₁` with its Haar probability to `K₂` with its Haar probability.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023) 109107,
  registered as `delorme-2023-spectral-theorem-langlands` (published PDF, whose page numbers are
  the PDF page numbers). §3.4, p.15, (3.7): for `φ ∈ A^2_P(G)` and `ψ ∈ A^{temp}_P(G)`,
  `(φ, ψ)^X_P = e^{-2ρ_P(X)} ∫_{M(𝔸)^1 × K} φ(exp_P X m_1 k) conj ψ(exp_P X m_1 k) dm_1 dk`,
  and the space `𝒜^{temp,c}_P(G)` of the `ψ` for which `X ↦ (φ, ψ)^X_P` vanishes for every
  `φ ∈ A^2_P(G)`. Delorme fixes one maximal compact subgroup `K` of `G(𝔸)` in good position
  with respect to `M_0` (p.2, and §2, p.5), and `H_P` is the left `U(𝔸)`-, right
  `K`-invariant map of that `K`.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
  `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, I.1.13, printed p.18 (PDF p.18). The
  measures: `meas(U(k) \ U(𝔸)) = 1`, `meas(K) = 1`, and the compatibility formula
  `∫_G f(g) dg = ∫_{U(𝔸) × M × K} f(u m k) m^{-2ρ_P} dk dm du` for a standard parabolic
  `P = MU`, which fixes the measure `dm` on `M` once `dg`, `du` and `K` are fixed.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*, Clay
  Math. Proc. 13 (2011), registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`
  (volume PDF; PDF page = printed page + 9). §2, p.311 (PDF p.320): `A_P`, the condition
  `φ(ag) = δ_P(a)^{1/2} φ(g)` for `a ∈ A_M` defining `A^n_P`, and
  `‖φ‖²_P = ∫_{A_M P U(𝔸) \ G(𝔸)} |φ(g)|² dg < ∞` defining `A^2_P`, with `K` in good position
  and Haar measures chosen compatibly with the Iwasawa decomposition.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`.
  §2.2, p.191: `X_P = U(𝔸) P(F) \ G(𝔸) = U(𝔸) M(F) \ G(𝔸)`, identified with the fibred
  product `(M(F) \ M(𝔸)) ×_{M(𝔸) ∩ K} K`, the space `A_P` of automorphic forms on `X_P`, and
  `φ_λ(g) = φ(g) m_P(g)^λ`, which depends on `K` through the Iwasawa factor `m_P(g)`.

## Correspondence with the sources

- **The pairing.** For `x = exp_P X ∈ 𝔄_P` (`positiveSplitComponent`, the positive real points
  of the split component `A_P`), `δinv x = x^{-2ρ_P} = e^{-2ρ_P(X)}`. So
  `δinv x * ∫ 𝓕.squareIntegrablePairingIntegrand K J x θ ψ` is Delorme's `(θ, ψ)^X_P` for the
  compact `K`, with Delorme's integral over `M(𝔸)^1 × K` written over
  `K × M(F) \ M(𝔸)^1`, as in the Markdown of `AdelicTemperedVanishingReduction`. The factor
  `e^{-2ρ_P(X)}` is kept here, because it is the factor that makes the comparison constant
  independent of `X`.
- **The heights.** `characterLog F P x ∈ 𝔞_P = Hom(X^*(P), ℝ)` is `H_P(x)` for `x ∈ P(𝔸)`. It
  equals `H_P^K(p(x))` for every Iwasawa compact `K` (`IsIwasawaCompact.height_map`). The
  Library's `StandardParabolicFamily.standardPositiveLog` proves that `characterLog` is a group
  isomorphism from `𝔄_P` onto `𝔞_P`. So for every `x ∈ 𝔄_P` and `v ∈ 𝔞_P` there is exactly one
  `x' ∈ 𝔄_P` with `H_P(x') = H_P(x) - v`.
- **The sign of the shift.** `Δ` is left `P(𝔸)`-invariant (see below), so it is a function on
  the classes in `U(𝔸) M(F) \ G(𝔸)`. Let `g = x m k₁` with `m ∈ M(𝔸)^1` and `k₁ ∈ K₁` satisfy
  `Δ(g) = v`. Then `H_P^{K₁}(g) = H_P(x)`, because `H_P` vanishes on `M(𝔸)^1` and `H_P^{K₁}` on
  `K₁`, so `H_P^{K₂}(g) = H_P(x) - v`. The Iwasawa decomposition for `K₂` and
  `M(𝔸) = 𝔄_P × M(𝔸)^1` write `g = u' x' m' k₂` with `u' ∈ U(𝔸)`, `x' ∈ 𝔄_P`, `m' ∈ M(𝔸)^1`
  and `k₂ ∈ K₂`, and then `H_P(x') = H_P^{K₂}(g) = H_P(x) - v`. The factor `u'` is in general
  not trivial: `g` need not lie in `M(𝔸) K₂`. What holds is that `g` and `x' m' k₂` have the
  same class in `U(𝔸) M(F) \ G(𝔸)`. The same computation with `K₁` and `K₂` exchanged gives the
  reverse inclusion: if `g = x' m' k₂` with `Δ(g) = v`, then `H_P^{K₁}(g) = H_P(x') + v = H_P(x)`
  and `g ∈ U(𝔸) x M(𝔸)^1 K₁`, since `characterLog` is injective on `𝔄_P`. So the classes of
  `x M(𝔸)^1 K₁` on which `Δ = v` are exactly the classes of `x' M(𝔸)^1 K₂` on which `Δ = v`.
  The integrands of assertion 4 are left `U(𝔸) M(F)`-invariant, so they are functions of these
  classes. This is the height relation in assertion 4. The measures on the two families of
  classes are compared below.
- **`A^2_P`.** `IsSquareIntegrableInducedForm` (module
  `Langlands.Global.AdelicSquareIntegrableInducedForms`) is Lapid's `A^2_P` for a compact `K`,
  with the `L²` condition written in Iwasawa coordinates on `K × [M]`, `[M] = A_M M(F) \ M(𝔸)`.
  The matrix representation `rho` gives the growth condition, and `hsmooth`, `hcalc` give the
  smoothness and `𝔷`-finiteness. Lapid's norm is an integral over `A_M U(𝔸) P(F) \ G(𝔸)` and does
  not involve `K`, while the Iwasawa-coordinate form does. Assertion 3 says that the
  Iwasawa-coordinate condition for `K₂` holds for the cut `φ_v` of a form that satisfies it for
  `K₁`.

## Why the statement holds (explanatory, not proved here)

The proposition is derived. None of the sources states it, because each fixes one compact. The
following argument is not formalized in this module.

**Assertions 1 and 2** are in the Library already. Let `K₁`, `K₂` be maximal with the same
infinite projection. `IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq` shows that
`K₁ ∩ K₂` is open in `K₁`. Given that, `IsIwasawaCompact.finite_range_height_sub` gives the
finite range of `Δ`, and `IsIwasawaCompact.exists_parameterTwist_clopen_decomposition` gives the
clopen fibres (module `Langlands.Global.AdelicEisensteinFiniteCompactChangeProof`).

**The left and right invariance of `Δ`.** `Δ(p(q) g) = Δ(g)` for `q ∈ P(𝔸)`, since both heights
add `log_P(q)` (`IsIwasawaCompact.height_map_mul`). `Δ(g k) = Δ(g)` for `k ∈ K₁ ∩ K₂`. And
`Δ(g)` depends only on the finite coordinate of `g`
(`IsIwasawaCompact.height_sub_pair_eq_of_infinite_eq`).

**Automorphy and the `A^n_P` condition of `φ_v`.** The automorphy is the cut of
`IsAutomorphicFunctionOn.indicator_finite`, applied as in the Library's proof of
`EisensteinFiniteCompactChangeStatement`. Maximality and equality of the infinite projections
give `K₁ ∩ G(𝔸_∞) = K₂ ∩ G(𝔸_∞)` (`IsMaximalCompactSubgroup.eq_comap_prod`), so the
archimedean finiteness subgroup is the same for `K₁` and `K₂`. The `A^n_P` condition passes to
`φ_v` because `Δ` is left `P(𝔸)`-invariant.

**The measure comparison.** Write `δ = δ_P` and `q : G(𝔸) → P(𝔸) \ G(𝔸)` for the quotient
map. Call `f : G(𝔸) → [0, ∞]` *`δ`-equivariant* if `f(p g) = δ(p) f(g)` for `p ∈ P(𝔸)`. For a
compact `K` with `P(𝔸) K = G(𝔸)` put `Λ_K(f) = ∫_K f(k) dk` (Haar probability). Fix Haar
measures `dg` on `G(𝔸)` and `du` on `U(𝔸)`, the same for both compacts. For `K = K₁, K₂` let
`μ_K` be the Haar measure on `M(𝔸)` compatible with `K` in the sense of MW I.1.13. (The
Library proves its existence: `iwasawaCompatibleMeasureExistence`, a proof of
`IwasawaCompatibleMeasureExistenceStatement`.) Then for every compactly supported continuous
`β ≥ 0` on `G(𝔸)`,

`∫_{G(𝔸)} β(g) dg = Λ_K(f^{μ_K}_β)`, where
`f^{μ_K}_β(g) = ∫_{M(𝔸)} ∫_{U(𝔸)} β(u m g) δ(m)⁻¹ du dμ_K(m)`,

and `f^{μ_K}_β` is `δ`-equivariant. Two Haar measures on `M(𝔸)` differ by a positive scalar.
Let `c > 0` be the scalar with `μ_{K₂} = c μ_{K₁}`, so that `f^{μ_{K₂}}_β = c f^{μ_{K₁}}_β`.
The claim is:

(★) `Λ_{K₁}(f) = c Λ_{K₂}(f)` for every lower semicontinuous `δ`-equivariant
`f : G(𝔸) → [0, ∞]`.

Choose a compactly supported continuous `β ≥ 0` on `G(𝔸)` with `β > 0` on `K₁`, and put
`b = f^{μ_{K₁}}_β`. Then `b` is continuous. For `k ∈ K₁` the integrand defining `b(k)` is
positive near `u = 1`, `m = 1`, so `b(k) > 0`. Since `b(p k) = δ(p) b(k)` and
`G(𝔸) = P(𝔸) K₁`, `b > 0` on all of `G(𝔸)`. Let `s` be a continuous function on the compact
space `P(𝔸) \ G(𝔸) = q(K₁)`. The function `s ∘ q` is left `P(𝔸)`-invariant, so
`f^{μ_K}_{β · (s ∘ q)} = (s ∘ q) · f^{μ_K}_β`. The compatibility formulas for `K₁` and `K₂`,
applied to `β · (s ∘ q)`, give

`∫_{K₁} s(q(k)) b(k) dk = ∫_{G(𝔸)} β(g) s(q(g)) dg = c ∫_{K₂} s(q(k)) b(k) dk`.

So the finite Borel measures `ν₁ = q_*(b dk)`, pushed forward from `K₁`, and
`ν₂ = q_*(c b dk)`, pushed forward from `K₂`, agree on continuous functions. The space
`P(𝔸) \ G(𝔸)` is compact and metrizable, because `G(𝔸)` is a second countable locally
compact group. On such a space a finite Borel measure is determined by its integrals of
continuous functions, so `ν₁ = ν₂`. Now let `f` be as in (★). The quotient `f / b` is
lower semicontinuous and left `P(𝔸)`-invariant. Hence `f = (F ∘ q) · b` for a function `F` on
`P(𝔸) \ G(𝔸)`, and `F` is lower semicontinuous, hence Borel, because `q` is open:
`{F > t} = q({f / b > t})`. Therefore
`Λ_{K₁}(f) = ∫ F dν₁ = ∫ F dν₂ = c Λ_{K₂}(f)`, with values in `[0, ∞]`.

The Iwasawa heights are continuous (`IsIwasawaCompact.continuous_height`, module
`Langlands.Global.AdelicEisensteinCompactBounds`). So (★) applies to the continuous
`δ`-equivariant function `f = e^{⟨2ρ_P, H_P^{K₂}⟩}`. It equals `1` on `K₂` and
`e^{-⟨2ρ_P, Δ⟩}` on `K₁`, which gives the explicit value
`c = ∫_{K₁} e^{-⟨2ρ_P, Δ(k)⟩} dk`. Applying (★) to `e^{⟨2ρ_P, H_P^{K₁}⟩}` instead gives
`c = (∫_{K₂} e^{⟨2ρ_P, Δ(k)⟩} dk)⁻¹`. This `c` is the positive constant of assertion 4. The
Lean statement asserts only its existence and positivity.

**Assertion 4.** Let `Θ = φ_v · conj ψ`. It is supported in `{Δ = v}`, continuous because the
fibre is clopen, and left `U(𝔸) M(F)`-invariant because `Δ` is left `P(𝔸)`-invariant. Since
`x ∈ 𝔄_P` lies in the image of the central split component of `M`, `x` commutes with `M(𝔸)`.
So the integrand does not depend on the representative `Quotient.out`, and it is continuous on
`K × M(F) \ M(𝔸)^1`. Let `Θ'` be any continuous function `G(𝔸) → [0, ∞)` that is left
`U(𝔸) M(F)`-invariant and supported in `{Δ = v}`, for example `|Θ|`. Put
`f(g) = ∫_{M(F) \ M(𝔸)^1} Θ'(m g) dm ∈ [0, ∞]`. By Tonelli and `x m = m x`, the integral of
`(k, m) ↦ Θ'(x m k)` over `K × M(F) \ M(𝔸)^1` is `∫_K f(x k) dk`. The function `f` has three
properties.

- It is lower semicontinuous, by Fatou's lemma, since `Θ'` is continuous and `G(𝔸)` is
  metrizable.
- It is left invariant under `P(𝔸)^1 = U(𝔸) M(𝔸)^1`: `Θ'` is left `U(𝔸)`-invariant,
  `M(𝔸)` normalizes `U(𝔸)`, and the quotient measure on `M(F) \ M(𝔸)^1` is right
  `M(𝔸)^1`-invariant because `M(𝔸)^1` is unimodular.
- It vanishes off `{Δ = v}`, because `Δ(m g) = Δ(g)`.

Let `a(g) ∈ 𝔄_P` be the element with `H_P(a(g)) = H_P^{K₁}(g)`. It depends continuously on `g`,
because `H_P^{K₁}` is continuous and the inverse of `H_P : 𝔄_P → 𝔞_P` is continuous (it is
the exponential map of the vector group `𝔄_P`). Put `f̃(g) = δ(a(g)) f(x a(g)⁻¹ g)`. Then `f̃`
is lower semicontinuous. It is `δ`-equivariant: for `p = u a₀ m₁` with `u ∈ U(𝔸)`, `a₀ ∈ 𝔄_P`
and `m₁ ∈ M(𝔸)^1` one has `a(p g) = a₀ a(g)`, and `x a(g)⁻¹ a₀⁻¹ p g ∈ P(𝔸)^1 x a(g)⁻¹ g`,
because `𝔄_P` is central in `M(𝔸)` and normalizes `U(𝔸)`. So (★) applies to `f̃`, and:

- `Λ_{K₁}(f̃) = ∫_{K₁} f(x k) dk`, since `a(k) = 1` for `k ∈ K₁`;
- for `k ∈ K₂` one has `H_P^{K₁}(k) = Δ(k)`, and `f(x a(k)⁻¹ k) = 0` unless `Δ(k) = v`. On
  `{Δ = v}`, `a(k) = a_v` with `H_P(a_v) = v` and `x a_v⁻¹ = x'`. Since `f(x' k) = 0` off
  `{Δ = v}` as well, `Λ_{K₂}(f̃) = e^{⟨2ρ_P, v⟩} ∫_{K₂} f(x' k) dk`.

Hence `∫_{K₁} f(x k) dk = c e^{⟨2ρ_P, v⟩} ∫_{K₂} f(x' k) dk` in `[0, ∞]`. For `Θ' = |Θ|`
this gives the equivalence of integrability. Now suppose both integrands are integrable. Write
`Θ = Θ₁ - Θ₂ + i (Θ₃ - Θ₄)` with the positive and negative parts of the real and imaginary
parts. Each `Θ_j` is continuous, nonnegative, left `U(𝔸) M(F)`-invariant, supported in
`{Δ = v}` and bounded by `|Θ|`. So the identity holds for each `Θ_j` with finite values, and
the linear combination gives `I_{K₁}(x) = c e^{⟨2ρ_P, v⟩} I_{K₂}(x')` for the Bochner integrals.
Because `e^{-⟨2ρ_P, H_P(x)⟩} e^{⟨2ρ_P, v⟩} = e^{-⟨2ρ_P, H_P(x')⟩}`, the identity takes the form
`δ(x)⁻¹ I_{K₁}(x) = c δ(x')⁻¹ I_{K₂}(x')`. When neither integrand is integrable, both Bochner
integrals are `0` and the identity is trivial.

**Assertion 3 (the `L²` condition).** Let
`h(g) = ∫_{[M]} δ(m)⁻¹ |φ_v(m g)|² dm ∈ [0, ∞]`. The integrand is invariant under `A_M` in `m`
by the `A^n_P` condition. The function `h` is lower semicontinuous by Fatou's lemma, since
`φ_v` is continuous. It is `δ`-equivariant: `φ_v` is left `U(𝔸)`-invariant, and right
translation on `[M]` by `M(𝔸) = A_M × M(𝔸)^1` preserves the pushed-forward norm-one quotient
measure `RestrictionSplitCentre.canonicalMeasure`. By Tonelli, `Λ_K(h)` is the Iwasawa-coordinate
`L²` integral of `φ_v` for `K`. Since `|φ_v| ≤ |φ|`, (★) gives
`Λ_{K₂}(h) = c⁻¹ Λ_{K₁}(h) ≤ c⁻¹ Λ_{K₁}(h_φ) < ∞`, where `h_φ` is the same function for `φ`.

## Hypotheses

- **Maximality and the same infinite projection.** These give the finite partition: `K₁ ∩ K₂`
  is open in `K₁`, so `Δ` is locally constant on `K₁`. They also make `Δ` a function of the
  finite coordinate, which keeps the cut smooth and `K_∞`-finite. No hypothesis says that `K₁`
  or `K₂` is in good position or conjugate to such a compact. The section "The compact
  subgroup" of the Markdown of `AdelicTemperedVanishingReduction` gives a `PGL₂` example (the
  stabilizer of an edge of the tree at a prime `p`) of a local maximal compact with
  `B(ℚ_p) K_p = PGL₂(ℚ_p)` that is not conjugate to a vertex stabilizer; such local factors
  differ from good-position ones only at finitely many finite places, which leaves the infinite
  projection unchanged.
- **`IsIwasawaCompact (𝓕.p J)`.** The heights `H_P^{K_i}` are those of `P = P_J`. A compact with
  `P_∅(𝔸) K = G(𝔸)`, the hypothesis of `WavePacketWeakConstantTermOrthogonalityStatement`, is
  Iwasawa for every standard `P_J ⊇ P_∅` (`IsIwasawaCompact.of_comp`, applied to the inclusion
  `P_∅ → P_J`).
- **Continuity and left `U(𝔸) M(F)`-invariance of `φ` and `ψ`.** These are the hypotheses for
  the quotient integration. Invariance makes the integrand independent of the representative in
  `M(F) \ M(𝔸)^1` and the slice integral left `P(𝔸)^1`-invariant. Continuity gives
  measurability on `K × M(F) \ M(𝔸)^1`. Every `φ ∈ A^2_P` and every automorphic form on
  `U(𝔸) M(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for `Γ`: its first component is the left
  invariance and the first component of its smoothness is continuity) satisfies them, and so
  do finite sums of such forms, for instance the weak constant terms
  `StandardParabolicFamily.IsWeakConstantTerm`. Assertion 4 does not require `φ ∈ A^2_P`.
- The unimodularity of `G(𝔸)` and `M(𝔸)^1` and the finiteness of the quotient measures, used
  above, hold because `G` and its Levi subgroups are connected reductive. These facts come with
  `𝓕` and are not separate hypotheses.

## Use: transferring (3.7) between compacts (explanatory)

Let `K₂` be a reference compact and `K₁` any maximal Iwasawa compact with the same infinite
projection. Suppose `𝓕.IsSquareIntegrableOrthogonal K₂ hK₂.isCompact rho hsmooth hcalc J ψ`
holds for a continuous left `Γ`-invariant `ψ`. Take `φ ∈ A^2_P` for `K₁` and `x ∈ 𝔄_P`. By
assertion 1, `φ = ∑_{v ∈ S} φ_v`. By assertion 3, each `φ_v` lies in `A^2_P` for `K₂`. Choose
`x'_v ∈ 𝔄_P` with `H_P(x'_v) = H_P(x) - v` (`standardPositiveLog`). The `K₂`-pairing of `φ_v`
with `ψ` at `x'_v` is integrable with integral `0`. By assertion 4, the `K₁`-pairing of `φ_v`
at `x` is integrable, and its integral is `0` because `δinv x ≠ 0`. The integrand is additive
in its first argument, so summing over `v ∈ S` gives
`𝓕.IsSquareIntegrableOrthogonal K₁ hK₁.isCompact rho hsmooth hcalc J ψ`. The same splitting
carries a pairing identity for `K₂` (for example the pairing of an Eisenstein packet test with
`ψ` written through (3.7)) to `K₁`, term by term, with the factor `c` and the shift of heights
by `v`. This transfer is not stated here.

## Provenance

Derived. The pairing and its measures are Delorme's (3.7) in the Library's normalization. The
spaces `A_P` and `A^2_P` are Lapid's §2 and Bernstein–Lapid's §2.2. The comparison constant
comes from MW I.1.13 applied to the two compacts with the same `dg` and `du`. The finite
partition is the Library's change of finite compact for parameter twists
(`EisensteinFiniteCompactChangeStatement` and its proof), stated here for the forms of `A^2_P`
and for the pairings of (3.7) instead of for the twists.

## Scope

The module states the comparison and does not prove it. It does not state the explicit value of
`c`, the transfer of `IsSquareIntegrableOrthogonal` described above, the archimedean change of
compact, or any comparison of Eisenstein series.
