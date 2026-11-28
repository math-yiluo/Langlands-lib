# Local boundedness and continuity of elliptic orbital integrals of coefficients of GL_n

Lean module: `Langlands.BaseChange.EllipticOrbitalCoefficientContinuityStatement`. The file
states the proposition `EllipticOrbitalCoefficientContinuityStatement.{u, uV}` and does not
prove it.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero, `0 < n`,
`G = GL_n(F)`, `Z` its center, and give `G ⧸ Z` its Borel σ-algebra
(`centralQuotientMeasurableSpace`). For

- every Haar measure `μ` on `G ⧸ Z`,
- every representation `π` of `G` on a complex vector space `W : Type uV` with
  `IsSquareIntegrable π` (admissible, unitary central character, coefficients square-integrable
  on `G ⧸ Z`) and `π.IsIrreducible`,
- every regular elliptic `γ` (`IsRegularElliptic`: characteristic polynomial separable and
  irreducible),
- every vector `v : W` and smooth functional `ℓ : SmoothDual π`,

there is a family `o : G → (G ⧸ Z → ℂ)` with `o x (gZ) = ℓ(π(g x g⁻¹) v)` for all `x, g ∈ G`,
an open set `U ∋ γ` and a real `B` such that

1. for every `x ∈ U` the function `o x` is `μ`-integrable and `∫_{G/Z} |o x| dμ ≤ B`;
2. the orbital integral `x ↦ ∫_{G/Z} o x dμ` is continuous at `γ` (as a function on `G`; at
   points `x` where `o x` is not integrable its value is the Bochner integral's `0`, which
   does not matter near `γ` by 1).

The value `ℓ(π(g x g⁻¹) v)` depends only on `gZ`, since central elements commute with `x`;
the family `o` records this descent.

The proposition has the hypotheses of `EllipticOrbitalCoefficientStatement` (module
`Langlands.BaseChange.EllipticOrbitalCoefficientStatement`, Clozel's Proposition 5 (ii)),
in the same order and with the same universe parameters `u`, `uV`, except the formal degree
and the character value, which it does not involve.

## Source and mathematical content

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101,
Birkhäuser (1991), §3, proof of Proposition 5 (ii), printed pp. 109–110 (PDF pp. 120–121).
Literature ID `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`,
SHA-256 `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.

Clozel writes `f` for a coefficient `g ↦ (u, π(g) v)` of the square-integrable `π`, a
Harish-Chandra Schwartz function, so that `f(1) = (u, v)`. For a test function `Φ` on `G`, his
Lemma 2 (a consequence of the Schur orthogonality relations), applied to `S = π(Φ)`, gives

`f(1) · trace π(Φ) = d(π) ∫_{Z\G} ∫_G f(x h x⁻¹) Φ(h) dh dx`,

where `dx` is the Haar measure on `Z\G` used to compute the formal degree `d(π)`. Clozel's
display (printed p. 109) is this identity under the normalization `(u, v) = 1`, which he
assumes immediately after it. He chooses a compact neighbourhood `ω` of `γ` in `G` contained
in the set of elliptic regular elements, applies the identity to the characteristic function
`Φ` of `ω`, and then has to justify interchanging the integrals. For this he states (printed
p. 110, "the arguments of Howe and Harish-Chandra mentioned after Lemma 1") that, since `|f|`
is again a Schwartz
function and the centralizer of an elliptic `h` is compact modulo `Z`, the inner integral
`∫_{Z\G} |f(x h x⁻¹)| dx` converges for `h ∈ ω`, behaves as the orbital integral of a
compactly supported function and is therefore locally constant in `h`, so that the double
integral `∫_ω ∫_{Z\G} |f(x h x⁻¹)| dx dh` is finite. After the interchange he lets `Φ` tend to
the Dirac distribution at `γ`, which uses the continuity at `γ` of the orbital integral
`h ↦ ∫_{Z\G} f(x h x⁻¹) dx`.

Correspondence:

- Clozel's integration variable `x ∈ Z\G` is `g ∈ G ⧸ Z` here (the two quotients agree since
  `Z` is central), and his element `h ∈ ω` is `x ∈ U` here, so his integrand `f(x h x⁻¹)` is
  `o x (gZ) = ℓ(π(g x g⁻¹) v)`. A smooth functional `ℓ` takes the place of `(u, ·)`; the
  coefficient `f(1)` is `ℓ(v)`. The normalization `(u, v) = 1` belongs only to Clozel's trace
  calculation: the proposition here concerns every vector `v` and every smooth functional
  `ℓ`, with no condition on `ℓ(v)`.
- Item 1 is the absolute convergence of the inner integral together with a bound uniform on a
  neighbourhood of `γ`; on a compact neighbourhood inside `U` it gives the finiteness of the
  double integral. Clozel obtains the bound from the local constancy of the absolute orbital
  integral on the compact `ω`.
- Item 2 is the continuity at `γ` used in the final limit. It is weaker than local constancy
  of the orbital integral near `γ`.
- Clozel's `ω` is a neighbourhood of `γ` in `G`, since `Φ` is a test function on `G`; the
  open set `U` is a neighbourhood of `γ` in `G` too. The statement does not require `U` to
  consist of regular elliptic elements, but `U` may always be shrunk into that set, which is
  open in `G` (`Langlands.BaseChange.isOpen_regularElliptic`, module
  `Langlands.BaseChange.RegularEllipticOpen`).

With the identity obtained from Lemma 2, items 1 and 2 give the
equality of Proposition 5 (ii): Fubini's theorem applies to test functions supported in a small
compact neighbourhood of `γ` inside `U`, and the limit over such neighbourhoods uses item 2.
