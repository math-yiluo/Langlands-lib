# Kottwitz's unramified representation `V(π_p, E_v)` and polynomial `P(π_p, E_v)`

Module `Langlands.Shimura.Unitary.KottwitzPolynomial`, namespace
`Langlands.Shimura.KottwitzDual`.

This module is the third unit of item 3 of Task 5424. It has two layers.

- For a dual-torus element `t̂`, it constructs Kottwitz's unramified
  representation `V = (r ∘ φ_{E_v}) ⊗ χ` of `W_{E_v}`, where `φ` sends
  Frobenius to `t̂ ⋊ Frob`, and the characteristic polynomial `P` of geometric
  Frobenius on `V` (Kottwitz 1992, printed pp.656-657). These operators depend
  on `t̂`.
- For a representation `π_p`, it defines existential relations: `V`, resp.
  `P`, is attached to `π_p` when it arises in this way from some
  principal-series parameter of `π_p` and some normalized lift `t̂` of it.

It proves:

- every such `P` is monic of degree `dim r`;
- the relations do not depend on the choice of `√p`: they hold for one square
  root of `p` exactly when they hold for the other, and `V` is literally
  unchanged when `√p` is negated and `t̂` is adjusted;
- `P` is invariant under twisted conjugation of `t̂`.

This module does not complete item 3. The relations do not by themselves
determine a unique `P(π_p, E_v) ∈ L[X]` for each `π_p`. The following are not
proved: existence of a parameter; independence of the lift `t̂`, of the Weyl
representative of the parameter, and of `θ` within the place `v`; and
Kottwitz's descent of `P` to `L[X]`. They are listed under "What is not claimed"
below and remain open work for the full task result.

It builds on three accepted units:

- `KottwitzDualGroup`: the dual group, the unramified L-group, and the
  Frobenius permutation attached to `θ : ℂ → Q̄_p`;
- `KottwitzRepresentation`: the representation `r`;
- Worker 8's `KottwitzChart` and `KottwitzPrincipalSeries`: standard unramified
  charts, the rational cocharacter lattice, `SqrtPrime`, and principal-series
  parameters.

Kottwitz names the twist `χ`. Here it is written `Z`, because `χ` already
denotes the unitarily normalized character of the torus.

## Conventions

The Library's naming is used: `E` is the totally real field (Kottwitz's `F₀`),
`K` the CM field (Kottwitz's `F`), and `S = (E →+* ℝ)`. The CM type `Φ` is
bundled as `IsCMSection E K Φ`. Kottwitz's function `i ↦ n(i)` is an input
`nfun : (K →+* ℂ) → ℕ` with `n(i) + n(ī) = n` (`hconj`). Examples are the
Library's `HarrisSignatureCharts.hodgeFunction` and `standardHodgeFunction`.
`cmHodge hΦ nfun` is this function read on the CM indices `S × Bool` (via
`cmFactorEmbeddingEquiv`), and `cmHodge_add` proves the identity `hsum` that
`KottwitzRepresentation` requires.

The prime is a natural number `p`, with the finite place
`rationalPrimePlace p` of `ℚ`. `c` is a standard unramified chart at that
place (Worker 8's item 1). `θ : ℂ →+* Q̄_p` determines three things:

- the place `v` of the reflex field;
- the Frobenius permutation `frobeniusPerm` of the complex embeddings of `K`;
- the places `w(i) = harrisPlace p θ i` of `K` above `p`.

`f = localDegree p θ nfun` is `hodgeOrbitDegree` of the Frobenius permutation
and `nfun`. By `KottwitzDualGroup.md`, it equals `[E_v : ℚ_p]` when `E_v/ℚ_p`
is unramified; that identification is documented there, not proved.

### Coefficients

Kottwitz (p.656) works over an algebraic closure `L̄` of the coefficient field
`L`:

- `Ĝ(L̄)`, a square root `√p` in `L̄`, and `V(π_p, E_v)` on an `L̄`-vector
  space;
- p.657: "the isomorphism class of `V(π_p, E_v)` is defined over `L`" and
  "`P(π_p, E_v)` has coefficients in `L`".

Accordingly, the relations below allow any field extension `Ω` of `L`, in which
the parameter `ξ` of Worker 8's `HasPrincipalSeriesParameter` takes values.
`s : SqrtPrime (rationalPrimePlace p) Ω` is a square root of `p` in `Ω`.
Kottwitz's case is `Ω = AlgebraicClosure L` (`IsKottwitzPolynomial`).

## The dual torus and the parameter

- `torusElement t` is `(ζ, (diag s_τ)_τ) ∈ Ĝ`, for `t = (ζ, (s_{τ,k}))`.
- `cocharPairing t a = ζ^{a₀} ∏_{τ,k} s_{τ,k}^{a_{τ,k}}`. This is the pairing
  `λ(t̂)` of `T̂` with a cocharacter `λ` in its free coordinates
  `(a₀, (a_{τ,k}))`, the coordinates of `KottwitzDualGroup.md`: `a₀` is the
  multiplier exponent and `a_{τ,k}` is the exponent at the CM-type embedding
  `Φ τ`.
- `twoRhoPairing a = Σ_{τ,k} (n − 1 − 2k) a_{τ,k}` is `⟨2ρ, λ⟩` for the upper
  triangular Borel subgroup. It is the formula Worker 8 uses for item 2.
- `embeddingCochar θ Φ m` writes a `ℚ_p`-rational cocharacter
  `m = (m_w, m_c) ∈ localCocharacters` in these coordinates:
  `a₀ = m_c`, `a_{τ,k} = m_{w(Φτ), k}`.
- `IsNormalizedLift c θ s ξ t` says that `t̂` lifts the unitarily normalized
  character `χ = ξ δ_B^{-1/2}` of Worker 8's principal-series character `ξ`:
  `λ(t̂) = ξ(λ(p)) · s^{⟨2ρ, λ⟩}` for all rational `λ`. This uses Kottwitz's
  `|x|^{1/2} = (√p)^{−val x}`, so `δ_B^{1/2}(λ(p)) = s^{−⟨2ρ, λ⟩}`.

This is the description of unramified Langlands parameters of tori in Borel
(1979, §9.5). An unramified character `χ` of `T(ℚ_p)` is a character of
`X_*(T)^Γ ≅ T(ℚ_p)/T(ℤ_p)`. Its parameter sends Frobenius to `t̂ ⋊ Frob`, where
`t̂` is any lift. The Frobenius here is the geometric one, matching the
generator of `LGroup` and the Library's `localGeometricFrobenius`.

A sanity check of this normalization uses the trivial representation (`ξ = 1`,
contained in the unnormalized induction of `1`). For it,
`t̂ = (1, (s^{n−1−2k})_{τ,k})` (that is, `2ρ(s)`) is a normalized lift, since
`λ(t̂) = s^{⟨2ρ, λ⟩}`. Write `d = hodgeDim h = dim S_K` and
`k_τ = h(τ, false)`. This check is not formalized.

- Split case. Suppose the Frobenius permutation `G` is the identity of
  `S × Bool`, for instance when `p` splits completely in `K`. Then `f = 1`, and
  `r(1 ⋊ Φ_v)` is the identity: `frobOp` reindexes by the identity and has no
  crossing factors. So `V(Φ_v) = s^d r(t̂)` is diagonal in the standard basis
  `⨂_τ e_{T_τ}` (`|T_τ| = k_τ`). Its eigenvalue on `⨂_τ e_{T_τ}` is
  `s^{d − Σ_τ Σ_{k ∉ T_τ} (n−1−2k)}`, an integral power of `p`. It is `p^d` at
  the highest-weight vector (`T_τ = [0, k_τ)`) and `1` at `T_τ = [n − k_τ, n)`.
  These are the expected weights of geometric Frobenius on the cohomology of
  the Shimura variety.
- General case. Here `r(1 ⋊ Φ_v)` is not the identity. `frobOp` permutes the
  tensor factors and applies the crossing map at crossings, so it permutes the
  standard basis lines up to sign. Kottwitz (1984, §2.3, printed p.296) keeps
  this permutation of the weight lines `ℂ_ν ↦ ℂ_{σν}`. The eigenvalues of
  `V(Φ_v)` are then not only powers of `p`. Example: `n = 2`, two real places
  interchanged by `G` without crossings, and `h` identically `1`. Then `f = 1`,
  `d = 2` and `t̂ = (1, diag(s, s⁻¹), diag(s, s⁻¹))`, so
  `V(Φ_v) = p (diag(s, s⁻¹) ⊗ diag(s, s⁻¹)) ∘ swap`. In the basis
  `e₀ ⊗ e₀, e₀ ⊗ e₁, e₁ ⊗ e₀, e₁ ⊗ e₁` its matrix is
  `[[p², 0, 0, 0], [0, 0, p, 0], [0, p, 0, 0], [0, 0, 0, 1]]`. The eigenvalues
  are `p², p, −p, 1`, and `P = (X − p²)(X − 1)(X² − p²)`. This pattern occurs
  for a real quadratic field `E` inert at `p` and a CM extension `K/E` split
  above `p`, with signatures `(1, 1)`, when `Φ` consists of the embeddings `i`
  such that `θ ∘ i` induces one fixed place of `K` above `p`. Kottwitz's
  Theorem 1 (1992, p.657)
  constrains the absolute values of the eigenvalues, not their signs.

## The norm and the restriction to `W_{E_v}`

- `frobNorm G x f` is `N_f(x) = x · σ(x) ⋯ σ^{f−1}(x)`, where `σ` is the action
  of `G` on `Ĝ`.
- `inl_mul_frob_pow`: `(x ⋊ Φ)^f = N_f(x) ⋊ Φ^f`.
- `restrictionHom_frobNorm`: the inclusion `^L(G_{E_v}) → ^LG` of
  `KottwitzDualGroup` sends `N_f(x) ⋊ Φ_v` to `(x ⋊ Φ)^f`. So `N_f(t̂) ⋊ Φ_v`
  is `φ_{E_v}(π_p)(Φ_v)`, the restriction of `φ(π_p)` to `W_{E_v}` evaluated at
  geometric Frobenius `Φ_v = Frob^f`.
- `frobNorm_twistedConj`: `N_f(y x σ(y)⁻¹) = y N_f(x) σ^f(y)⁻¹`.

## `V` and `P` for a dual-torus element

The hypotheses are those of `kottwitzRep`: `h`, `hsum`, and `hGf` (`G^f`
preserves `h`). In the application, `G = frobeniusCMPerm hΦ θ`,
`f = localDegree`, and `hGf` is `cmHodge_frobenius_pow`, which comes from
`hodgeOrbitDegree_preserves`.

- `hodgeDim h = Σ_τ n(Φτ) n(Φτ̄)` is `dim S_K = ⟨2ρ, μ⟩`.
- `frobeniusElement G f x = N_f(x) ⋊ Φ_v`.
- `kottwitzV h hsum G f hGf s x : ℤ →* Aut(W)` is the unramified
  representation of `W_{E_v}`, through its unramified quotient `ℤ` (generator
  `Φ_v`). It sends `Φ_v` to `Z(Φ_v) · r(N_f(x) ⋊ Φ_v)`, with
  `Z(Φ_v) = s^{f · dim S}` (Kottwitz's `(√p)^{[E_v:ℚ_p] dim S_K}`).
  `kottwitzFrobenius` is its value at `Φ_v`, and `kottwitzFrobenius_eq`
  unfolds it.
- `kottwitzBasis n L k` is the standard basis `⨂_τ e_{T_τ}` of
  `W = ⨂_τ ⋀^{k τ} Lⁿ` (Mathlib's `Basis.piTensorProduct` of the exterior
  power bases).
- `kottwitzCharpoly` is the characteristic polynomial of the matrix of
  `V(Φ_v)` in this basis, i.e. `det(X − V(Φ_v))`. Mathematically this is the
  basis-independent characteristic polynomial (for any finite free module,
  Mathlib's `LinearMap.charpoly_toMatrix` identifies the matrix version in any
  basis with `LinearMap.charpoly`). The matrix form is used because
  `LinearMap.charpoly` cannot be applied to `W` in Lean. The `AddCommGroup`
  structure Mathlib puts on `PiTensorProduct`
  (`Module.addCommMonoidToAddCommGroup`) does not unify with the module
  structure that `LinearMap.charpoly` expects.

Proved properties:

- `kottwitzCharpoly_monic`: `P` is monic.
- `kottwitzCharpoly_natDegree`: `P` has degree
  `kottwitzDim n k = ∏_τ C(n, k τ)`, which is `dim r = dim W`
  (`card_kottwitzBasisIndex`).
- `kottwitzCharpoly_twistedConj`: `P(y x σ(y)⁻¹) = P(x)`. The proof conjugates
  by `r(y ⋊ 1)`, using `charpoly_toMatrix_conj`. So `P` only depends on the
  `Ĝ`-conjugacy class of `φ(Frob) = x ⋊ Frob`, as Kottwitz requires
  ("well-defined up to conjugation by `Ĝ(L)`").

## Independence of `√p`

- `epsilonHat` is `ε̂ = (2ρ)(−1)`, the central element
  `(1, ((−1)^{n−1})_τ)` of `Ĝ`; `cocharPairing_epsilonHat` gives
  `λ(ε̂) = (−1)^{⟨2ρ, λ⟩}`.
- `IsNormalizedLift.neg`: if `t̂` is a normalized lift for `s`, then `t̂ ε̂` is
  one for `−s`.
- `kottwitzFrobenius_neg` and `kottwitzV_neg` prove that `V` is literally
  unchanged: `V(−s, x ε̂) = V(s, x)`. The ingredients are:
  - `ε̂` is central and fixed by the action (`epsilonElement_commute`,
    `dualAction_epsilonElement`), so `N_f(x ε̂) = N_f(x) ε̂^f`;
  - `r(ε̂)` is the scalar `∏_τ ((−1)^{n−1})^{n(Φτ̄)}` (`dualRep_epsilonElement`);
  - the sign `(−1)^{f(dim S + (n−1) Σ_τ n(Φτ̄))}` is `1`, since
    `m k + (m + k − 1) k` is even (`even_hodge`, `sign_cancel`).

## The relations for a representation `π_p`

`π` is a smooth representation of `G(ℚ_p)` over `L`.

- `kottwitzRepresentationOf θ hΦ nfun hconj s t` and
  `kottwitzPolynomialOf θ hΦ nfun hconj s t` are `V` and `P` for the
  dual-torus element `t̂`. `kottwitzPolynomialOf_eq` says `P` is the
  characteristic polynomial of `V(Φ_v)`.
- `IsKottwitzRepresentationOver c θ hΦ nfun hconj π Ω s V` says: for some
  `ξ : T(ℚ_p) → Ωˣ` with `c.HasPrincipalSeriesParameter π ξ`, and some
  normalized lift `t̂` of `ξ`, `V = kottwitzRepresentationOf … s t̂`.
- `IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P` is the same with
  `P = kottwitzPolynomialOf … s t̂ ∈ Ω[X]`. `isKottwitzPolynomialOver_iff` says
  it holds exactly when `P` is the characteristic polynomial of `Φ_v` on some
  `V` with `IsKottwitzRepresentationOver`.
- `IsKottwitzPolynomial c θ hΦ nfun hconj π s P` is the version for
  `P ∈ L[X]`: its image in `L̄[X]` (`L̄ = AlgebraicClosure L`) satisfies
  `IsKottwitzPolynomialOver`.

Proved properties:

- `IsKottwitzPolynomialOver.monic`, `IsKottwitzPolynomialOver.natDegree_eq` and
  `IsKottwitzPolynomial.monic_and_natDegree`: `P(π_p, E_v)` is monic of degree
  `dim r`.
- `isKottwitzRepresentationOver_iff_of_sqrtPrime`,
  `isKottwitzPolynomialOver_iff_of_sqrtPrime` and
  `isKottwitzPolynomial_iff_of_sqrtPrime`: the relations hold for one square
  root of `p` exactly when they hold for the other. This is Kottwitz's
  independence of `√p` (p.656). It uses `SqrtPrime.eq_or_eq_neg` (the square
  roots of `p` in a field are `±s`) and `ε̂`.
- `IsKottwitzPolynomialOver.of_equiv`: only the isomorphism class of `π`
  matters.

## What is not claimed

- Existence of a parameter `ξ` for a spherical `π`, and its uniqueness up to
  the Weyl group (Satake). These are neither assumed nor proved; the relations
  only name `V` and `P` when a parameter exists. No structure field stores a
  parameter or a polynomial.
- Independence of the lift `t̂`. Over an algebraically closed `Ω`, two lifts
  differ by an element of `ker(T̂ → Hom(X_*(T)^Γ, Ωˣ)) = {y σ(y)⁻¹}` (the
  quotient `T̂/(1 − σ)T̂` is the torus with character group `X_*(T)^Γ`). So
  `kottwitzCharpoly_twistedConj` gives independence of the lift. This
  derivation is documented, not formalized.
- Invariance of `P` under Worker 8's Weyl equivalence of parameters.
- Kottwitz's descent: the existence of `P ∈ L[X]` for `π` irreducible over
  `L̄` (p.657). `IsKottwitzPolynomial` characterizes `P` but does not prove it
  exists.
- Independence of `θ` among the embeddings inducing the same place `v`.
- `localDegree p θ nfun = [E_v : ℚ_p]`.

## Sources

- R. E. Kottwitz, *On the λ-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), §1, printed pp.656-657
  (`kottwitz-1992-lambda-adic-simple-shimura`). Covered there: the choice of
  `√p` and `|x|^{1/2} = (√p)^{−val x}`; the unramified `φ(π_p)` up to
  `Ĝ`-conjugacy and its restriction to `W_{E_v}`; `V(π_p, E_v) =
  (r ∘ φ_{E_v}(π_p)) ⊗ χ` with `χ(Φ_v) = (√p)^{[E_v:ℚ_p] dim S_K}`; the
  independence of `√p`; `P(π_p, E_v)` as the characteristic polynomial of
  `Φ_v`; and the coefficients in `L` and the `L̄` setting.
- R. E. Kottwitz, *Shimura varieties and twisted orbital integrals*, Math.
  Ann. 269 (1984), §2.1, printed pp.293-294, and §2.3, printed pp.295-296
  (`kottwitz-1984-shimura-varieties-twisted-orbital-integrals`): unramified
  parameters `φ(σ) = t ⋊ σ` with values in `W^{un} ⋉ Ĝ`, and the
  representation `r_μ`.
- A. Borel, *Automorphic L-functions*, Corvallis Part II (1979), §9.5, printed
  pp.42-43 (`borel-1979-automorphic-l-functions`): unramified characters of
  unramified tori, `T(k)/°T(k) ≅ X_*(T)^Γ`, and the parameters `t ⋊ Fr`.
