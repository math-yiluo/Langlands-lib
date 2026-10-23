# Tate's `ε₁` normalization and its Galois equivariance

Worker 33 wrote this module for task `e534647a`. It covers Tate 1979,
(3.6.10) and (3.6.11), in the nonarchimedean case. These give the explicit
rank-one formula for the local constant `ε₁(V, ψ) = ε_D(V, ψ, dx₁)`, where
`dx₁` gives the ring of integers volume one, and its compatibility with every
field automorphism `σ` of `ℂ`: `ε₁(V^σ, ψ^σ) = ε₁(V, ψ)^σ`. The main
declaration is `Langlands.LocalFactor.EpsilonOneStatement`. It is a
proposition only. No local-constant system is constructed or chosen, nothing
is proved, and nothing is assumed as an axiom.

## Objects

Everything except one abbreviation comes from the published Library.

- `PadicField.TopologicalData T` of a p-adic field `F`, with:
  - `T.ord`, the integer-valued normalized additive order
    (`T.ord π = 1`, `T.ord 0 = 0`), and `T.residueCardinality = q`;
  - `T.principalUnits m`, the subgroup `U^m` of `F^×` defined by
    `T.discreteValuation u = 1` and
    `T.discreteValuation (u - 1) ≤ WithZero.exp (-(m : ℤ))`.
    The first condition restricts to integral units; the second includes
    `u = 1` at every level because `T.discreteValuation 0 = 0`.
    At level zero, `U^0 = Oˣ`;
  - `T.additiveConductor ψ`, Tate's `n(ψ)`: the largest `n` with
    `ψ(π^(-n) O) = 1`;
  - `T.multiplicativeConductor χ`, Tate's `a(χ)`: the least `m ≥ 0` with `χ`
    trivial on `U^m`. It is `0` exactly when `χ` is unramified;
  - `T.integerVolume μ`, the volume `μ(O)` of the ring of integers;
  - `T.abelianEpsilonExpression χ ψ μ`, Tate's rank-one constant
    `ε(χ, ψ, dx)` of (3.2.6.1) and (3.2.6.2). Let `c` have order
    `n(ψ) + a(χ)`. If `χ` is unramified it is `χ(c) / ‖c‖ · μ(O)`. If `χ` is
    ramified it is the integral of `χ⁻¹(x) ψ(x)` over `c⁻¹ Oˣ` for `μ`.
- `HarmonicAnalysis`: quasicharacters `χ` (continuous homomorphisms
  `F^× → ℂ^×`), unitary additive characters `ψ` (continuous nontrivial
  characters `F → S¹`, with complex values `ψ.complex`), and additive Haar
  measures `μ`.
- `CommonClosure`: the finite intermediate extensions `E : Extension F` of
  the algebraic closure of `F`, their Weil subgroups `W_E` (`weilSubgroup F E`),
  the canonical topological data `fieldData F E`, the additive characters and
  Haar measures of each `E`, and the class
  `ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) ⟨A, hA⟩`
  of a genuine continuous representation `A` in the exact virtual group
  `Virtual F E`.
- `NonabelianSystem`: an assignment `ε_E(x, ψ, μ)` of complex units, and the
  system property `IsSystem F e ε` for a supplied reciprocity family `e`. It
  consists of normalized reciprocity, additivity, Haar scaling, degree-zero
  induction with arbitrary Haar measures, and rank-one agreement with
  `abelianEpsilonExpression` through the reciprocity map.
- `FiniteRepresentation ℂ W_E`: finite-dimensional complex representations of
  `W_E` on an actual carrier space, and `IsContinuous`, continuity of the
  action for the usual topology on endomorphisms.

The only new declaration besides the propositions is the abbreviation
`UnitQuotient T a = U^0 / U^a`. It is the quotient of `Oˣ` by `U^a`
(`subgroupOf` views `U^a`, which lies in `U^0`, inside `U^0`). It is the index
set `Oˣ mod π^a` of Tate's sum.

## The statement

`EpsilonOneStatement` says: for every prime `p` and every p-adic field `F`,

- for every topological datum `T` of `F`, the rank-one formula and its
  Galois equivariance hold (clauses 1 and 2), and
- every local-constant system on the common closure of `F` is Galois
  equivariant at every intermediate field (clause 3).

`ε₁` is not a new definition. Every clause quantifies over Haar measures `μ`
with `integerVolume μ = 1`, that is, over Tate's `dx₁`, and evaluates the
existing objects there. All clauses live in the namespace
`Langlands.LocalFactor.EpsilonOne`.

1. `RankOneFormulaStatement T` (Tate (3.6.11)). Let `χ` be a quasicharacter,
   `ψ` an additive character and `μ` a Haar measure with `μ(O) = 1`. Write
   `a = a(χ)` and `n = n(ψ)`. Let `c ∈ F^×` have `ord c = n + a`, and let
   `r : Oˣ/U^a → Oˣ` be any map sending each class to a representative of
   it. Then

   `abelianEpsilonExpression χ ψ μ = χ(c) · q^n · ∑_(x ∈ Oˣ/U^a) χ(r x)⁻¹ · ψ(r x / c)`.

   The sum is a `finsum` over the finite quotient, and `q^n` is an integer
   power.
2. `AbelianGaloisStatement T` (rank-one case of Tate (3.6.10)). Let `σ` be
   any field automorphism of `ℂ`, not necessarily continuous. Let `χ, χ'` be
   quasicharacters with `χ'(u) = σ(χ(u))` for all `u ∈ F^×`, and let `ψ, ψ'` be
   additive characters with `ψ'(y) = σ(ψ(y))` for all `y ∈ F`. Then for every
   Haar measure `μ` with `μ(O) = 1`,

   `abelianEpsilonExpression χ' ψ' μ = σ(abelianEpsilonExpression χ ψ μ)`.
3. `GaloisEquivarianceStatement F` (Tate (3.6.10)). Let `e` be a reciprocity
   family and `ε` an assignment with `IsSystem F e ε`. Let `E` be an
   intermediate field and `σ` a field automorphism of `ℂ`. Let `ψ, ψ'` be
   additive characters of `E` with `ψ'(y) = σ(ψ(y))` for all `y ∈ E`, and let
   `μ` be a Haar measure on `E` with `μ(O_E) = 1`. Let `A, B` be genuine
   continuous representations of `W_E`. Suppose `f : A → B` is a bijective
   `σ`-semilinear map (`f(z v) = σ(z) f(v)`) with `f(g v) = g f(v)` for every
   `g ∈ W_E`. Then

   `ε_E([B], ψ', μ) = σ(ε_E([A], ψ, μ))`.

### Design choices

- **Conjugates are described by relations.** The Library has no
  construction of the conjugate representation `V^σ = ℂ ⊗_(σ, ℂ) V` or of the
  conjugate characters `σ ∘ χ`, `σ ∘ ψ`. The clauses therefore quantify over
  objects with the conjugate values. Such objects always exist, so nothing is
  lost:
  - `σ ∘ χ` is a quasicharacter. The image of the compact group `Oˣ` under
    `χ` is finite, so `χ` has open kernel on `Oˣ`. So has `σ ∘ χ`, and the
    value at a uniformizer is unconstrained.
  - `σ ∘ ψ` is an additive character. `ψ` is trivial on `π^(-n(ψ)) O`, and on
    each lattice `π^(-m) O` it takes `p`-power roots of unity as values. `σ`
    permutes roots of unity, so `σ ∘ ψ` is again unitary, locally constant
    and nontrivial.
  - If `f : A → B` is as in clause 3, then `z ⊗ v ↦ z · f(v)` is an isomorphism
    of representations `ℂ ⊗_(σ, ℂ) A → B`. Conversely `v ↦ 1 ⊗ v` is such an
    `f` for `B = ℂ ⊗_(σ, ℂ) A`. Since `ε` only sees the class of `B`, clause 3
    is exactly Tate's `ε₁(V^σ, ψ^σ) = ε₁(V, ψ)^σ`.
- **Continuity of `B`.** The hypothesis that `B` is continuous makes its class
  available in the continuous virtual group. It holds automatically. Inertia
  is an open profinite subgroup of `W_E`, so `A` has open kernel on it, and
  `B` has the same kernel. Hence `B` is locally constant on inertia, and so
  continuous on `W_E`, whose cosets of inertia are open.
- **Every automorphism `σ`.** `σ : ℂ ≃+* ℂ` is any field automorphism.
  Tate's point is that this includes discontinuous `σ`. Those need not fix
  real numbers, which is why `ε₁` uses the rational volume `μ(O) = 1`.
- **Genuine representations.** Clause 3 is stated for genuine
  representations, where conjugation is described by `f`. The virtual form
  follows at once: both sides are multiplicative in the class, by the
  additivity in `IsSystem`.
- **Every intermediate field.** Tate states (3.6.10) over the base field.
  Clause 3 holds at every finite intermediate field `E` of the common
  closure. At `E = F` it is Tate's statement.
- **All choices of `c` and `r`.** Clause 1 holds for every `c` of the right
  order and every system of representatives. This records Tate's "`c` as in
  (3.2.6)" and his sum over "`u ∈ O^* mod π^(a(χ))`". The rank-one clauses
  concern only the explicit abelian expression, so they are stated for every
  topological datum of every p-adic field, with no system.
- **A misprint in (3.6.11).** The printed display reads
  `ε₁(χ, ψ) = χ(c) q^(n(ψ)) ∑_(u ∈ O^* mod π^(a(χ))) χ(u)(u/c)`: the
  character `ψ` and the inverse on `χ(u)` are missing. Tate says the formula
  follows from (3.2.6.1) and (3.2.6.2), and (3.2.6.2) integrates
  `χ⁻¹(x) ψ(x)` over `c⁻¹ O^*`. This gives `χ⁻¹(u) ψ(u/c)`, which clause 1
  uses. The computation is in the next section.

### Why the clauses hold

This explains the statement only. None of it is a Lean proof.

- **Clause 1.** For ramified `χ`, substitute `x = u/c` with `u ∈ Oˣ` in
  (3.2.6.2). Then `d(u/c) = ‖c‖⁻¹ du = q^(n + a) du` and
  `χ⁻¹(u/c) = χ(c) χ⁻¹(u)`. The function `u ↦ χ⁻¹(u) ψ(u/c)` is constant on
  cosets of `U^a`: `χ` is trivial on `U^a`, and for `t ∈ O` the element
  `u π^a t / c` has order at least `-n`, so `ψ` is trivial on it. Each coset
  has volume `q^(-a)`. Hence the integral is
  `χ(c) q^(n + a) q^(-a) ∑ χ⁻¹(u) ψ(u/c)`. For unramified `χ` the quotient
  has one class, `χ⁻¹(r x) = 1` and `ψ(r x / c) = 1`, and (3.2.6.1) gives
  `χ(c) q^n` at `μ(O) = 1`.
- **Clause 2.** `χ'` and `χ` have the same kernel, so `a(χ') = a(χ)`.
  Likewise `n(ψ') = n(ψ)`. Apply clause 1 to both pairs with the same `c` and
  `r`. `σ` is additive and multiplicative on the finite sum, and it fixes the
  rational number `q^n`.
- **Clause 3.** This is Tate's argument "by unicity (2.3.3) and the formula
  (3.6.11)". For a system `ε`, put
  `ε^σ_E(x, ψ, μ) = σ⁻¹(ε_E(x^σ, σ ∘ ψ, μ₁)) · μ(O_E)^(deg x)`, where `μ₁` is
  `μ` scaled to `μ₁(O_E) = 1`. The real factor stays outside `σ⁻¹`. Then
  `ε^σ` satisfies each part of `IsSystem`:
  - normalized reciprocity concerns `e` only;
  - additivity holds because conjugation preserves short exact sequences;
  - Haar scaling holds by construction;
  - degree-zero induction holds because conjugation commutes with induction
    and with pulling `ψ` back along the trace, and in degree zero the measures
    do not matter;
  - the rank-one law follows from clause 2, since `(χ ∘ rec)^σ = (σ ∘ χ) ∘ rec`
    and the abelian expression is proportional to `μ(O)`.

  Uniqueness of systems then gives `ε^σ = ε`. This is Tate's (2.3.3), and
  the Library states it as the proposition `NonabelianSystem.Unique`. At
  `μ = μ₁` this is clause 3.

### Related items not restated

- Tate's paragraph after (3.6.11) defines `ε₁(V, ψ)` in every coefficient
  field `E` of characteristic 0, using the equivariance, and says it is
  inductive in degree 0 there. The common-closure interface has complex
  coefficients only, so this is not stated.
- The global remark after (3.6.10): the global constant is `a⁻¹` times the
  product of the local `ε₁(V_v, ψ_v)`. It is global and outside this local
  module.
- In the archimedean case `dx₁` is a definition only (the measures of
  (3.2.4) and (3.2.5)), and the equivariance is claimed only in the
  nonarchimedean case. The common closure here is p-adic.
- Tate's remark that `ε_L(V^σ, ψ^σ)` is in general not `ε_L(V, ψ)^σ` is a
  negative remark, not an identity. It is not formalized.
- Tate's closing remark that the `ε_D` system works over any coefficient
  field of characteristic 0, once Haar measures with values in it are
  defined, is not stated.

## Sources

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
  J. Tate, *Number theoretic background*, Corvallis Part II (1979). PDF page =
  printed page + 9. All formula pages were checked visually.
  - Printed p.18 (PDF p.27): (3.6.10) `ε₁(V, ψ) = ε_D(V, ψ, dx₁)`, with `dx₁`
    giving `O` measure 1 in the nonarchimedean case. Then the claim
    `ε₁(V^σ, ψ^σ) = ε₁(V, ψ)^σ` for all automorphisms `σ` of `ℂ` in the
    nonarchimedean case, "clear by unicity (2.3.3) and the formula" (3.6.11).
    The remarks listed above under "Related items" are also on this page.
  - Printed p.17 (PDF p.26), last lines, continued on p.18: the remark on
    discontinuous `σ` and Langlands' `ε_L`.
  - Printed p.13 (PDF p.22): (3.2.6) defines `n(ψ)`, `a(χ)` and `c` of
    valuation `n(ψ) + a(χ)`, and gives (3.2.6.1)
    `ε(χ, ψ, dx) = χ(c) ‖c‖⁻¹ ∫_O dx` for unramified `χ`.
  - Printed p.14 (PDF p.23): (3.2.6.2)
    `ε(χ, ψ, dx) = ∫_(c⁻¹ O^*) χ⁻¹(x) ψ(x) dx` for ramified `χ`.
  - Printed p.12 (PDF p.21): Remark (2.3.3), uniqueness of a function
    inductive in degree 0 given its values on quasicharacters.
