# Absolute convergence of Eisenstein series

Module `Langlands.Global.AdelicEisensteinConvergenceStatement` defines three
helpers and states `Langlands.Global.EisensteinAbsoluteConvergenceStatement`
as a proposition definition. It supplies no proof.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  chapter file `06.1_pp_78_100_Definitions.pdf`, II.1.5, printed p.85: there
  is a positive open cone of real parts such that for parameters in it the
  series defining the Eisenstein series converges normally for `g` in a
  compact set and the parameter in a neighborhood.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2, p.191:
  for `φ ∈ 𝒜_P` the series (2.1) converges absolutely and locally uniformly
  in `g` and `λ` for `Re λ` sufficiently regular in the positive Weyl chamber
  of `𝔞_P^*`, citing MW II.1.5.

## Helpers

- `realParameterRestriction s : X^*(P) ⊗ ℝ → X^*(A) ⊗ ℝ`, for `s : A → P`
  with `A` commutative, is the real scalar extension of restriction of
  characters along `s`, followed by the existing identification
  `rationalCharacters.equivCharacterLattice` of the characters of `A` with
  its character lattice. The target is the existing
  `RealTorusSpace.Vstar A`.
- `ParabolicRootPresentation.unipotentRoots r`, for a presentation
  `r : ParabolicRootPresentation p l a` (published module
  `Langlands.GroupScheme.Rational.ParabolicRootPresentation`), is the set of
  nonzero characters `f ≫ χ` of `A` with `χ` a positive relative root of the
  presentation's maximal split torus `T` (positive for its generic cocharacter
  `ν`), where `f : A → T` is the presentation's factorization. These are the
  roots of `A` in the Lie algebra of the unipotent radical: the roots of `T`
  in the Levi restrict to zero on its split component `A`.
- `ParabolicRootPresentation.IsRegularParameter r hA hT R λ`, for a complex
  parameter `λ ∈ X^*(P) ⊗ ℂ` and a real `R`, says `R < B(Re λ|_A, α)` for
  every `α ∈ r.unipotentRoots`. Here `B` is the existing positive definite
  form `Langlands.Plancherel.weylInducedCharacterForm hA hT f i` on
  `X^*(A) ⊗ ℝ`, induced from the relative-Weyl-invariant form of `T`,
  `Re λ` is `parameterRealPart`, and `Re λ|_A` is
  `realParameterRestriction (a ≫ l)`. The later Eisenstein and intertwining
  statements use the same predicate for "`Re λ` sufficiently regular".

## Statement

The statement quantifies a number field `F`; group schemes `G`, `P`, `M`,
`U` and a commutative group scheme `A` over `F`; a closed immersion
`p : P → G`; maps `iU : U → P`, `l : M → P` and `a : A → M`; a presentation
`r : ParabolicRootPresentation p l a`; the instances that `r`'s torus
inclusion and `f` are monomorphisms and that the relative Weyl group of `r`
is finite; and proofs `hA`, `hT` that `A` and `T` are split tori. It assumes
that `G` is connected reductive and that `iU` is a (geometric) unipotent
radical of `P`. The presentation itself says that `p` is a parabolic, equal to
the standard parabolic of `(T, ν, J)`, that `l` is a rational Levi subgroup
and that `a` is its split component.

It then quantifies a subgroup `K` of `G(𝔸)` with `P(𝔸)K = G(𝔸)`
(`hK : IsIwasawaCompact p K`, which also records compactness) that is a
maximal compact subgroup (`IsMaximalCompactSubgroup F G K`), a closed matrix
embedding `rho` (`IsClosedSubgroup rho`), the smooth-structure data
`hsmooth`, `hcalc`, and a function `φ` that is an automorphic form on
`U(𝔸)M(F) \ G(𝔸)`: `IsAutomorphicFunctionOn` for the subgroup
`parabolicQuotientSubgroup F p iU l` (the published `U(𝔸)M(F)` of
`Langlands.Global.AdelicParabolicQuotient`) and for the archimedean part
`K ∩ G(𝔸_∞)` of `K` (`K.comap (ofInfinite F G)`), MW I.2.17. As in BL §2.1,
one maximal compact `K` serves both for `m_P` and for `K`-finiteness. These
are the hypotheses under which `𝒜_P` is the source's space.

The conclusion: there is a real `R` such that for every compact `C ⊆ G(𝔸)`,
every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every compact
`Λ ⊆ ℂⁿ` on which every `λ = e(s)`, `s ∈ Λ`, is `R`-regular
(`r.IsRegularParameter hA hT R λ`: `R < B(Re λ|_A, α)` for all
`α ∈ r.unipotentRoots`), there is a summable `b` on `P(F) \ G(F)` with
`‖φ_λ(γ_c g)‖ ≤ b(c)` for every coset `c`, every `g ∈ C` and every `s ∈ Λ`.
The terms `φ_λ(γ_c g)` are `hK.eisensteinTerm φ λ g c`.

## Correspondence with the source

- Normal convergence: one summable majorant on `C × Λ` is MW's "converges
  normally for `g` in a compact set and the parameter in a neighborhood"; it
  gives absolute and locally uniform convergence (BL).
- The region. BL require `⟨Re λ, α^∨⟩ ≫ 0` for the simple roots `α ∈ Δ_P`.
  For any positive definite form `B_T` invariant under the relative Weyl
  group, the reflection in `α` is orthogonal, so
  `⟨x, α^∨⟩ = 2 B_T(x, α)/B_T(α, α)`. The form `B` on `X^*(A) ⊗ ℝ` is `B_T`
  on the `B_T`-orthogonal lifts, and a parameter of `P` restricted to `A`
  lifts orthogonally to the roots of the Levi. Hence `⟨Re λ, α^∨⟩ ≫ 0` for
  the simple roots of `A` in `U` is equivalent to `B(Re λ|_A, α) ≫ 0` for
  them, and, since every root of `A` in `U` is a nonnegative combination of
  simple ones with a positive coefficient, to `B(Re λ|_A, α) > R` for all
  `α ∈ r.unipotentRoots` with `R` large. This is explanatory and not proved
  here. The same kind of region is used for local intertwining integrals in
  `Langlands.Representation.Plancherel.ParabolicRootCone`.
- "Sufficiently regular" is the existential `R`, which may depend on `φ`, as
  in MW ("there exists a cone").
- The compact subgroup. BL (§2.1, p.190) and MW (I.1.4) fix `K` in good
  position with respect to a minimal Levi `M₀`; here `K` is any maximal
  compact subgroup with `P(𝔸)K = G(𝔸)`. This reduces to their case. Such a
  `K` is `K_∞ × K_f` with `K_∞` maximal compact in `G(F_∞)` and `K_f` open
  in `G(𝔸_f)`. Fix `K₀` in good position. Then `K_∞ = nK₀,∞n⁻¹` for some
  `n ∈ G(F_∞)`, and the difference of the two height maps at the finite
  places is a function on the finite set
  `P(𝔸_f) \ G(𝔸_f) / (K_f ∩ K₀,f)`. Hence `φ_λ` computed with `K` is a finite
  sum `∑ j, exp⟨λ, c_j⟩ · (φ_j)_λ(· n)` with `(φ_j)_λ` computed with `K₀`,
  where `φ_j` is the product of `φ(· n⁻¹)` and the indicator of a left
  `P(𝔸_f)`-invariant open and closed set, and `φ_j ∈ 𝒜_P` for `K₀`. The
  Eisenstein terms, series and intertwining integrals for `K` are the
  corresponding finite combinations of those for `K₀`, with coefficients
  entire in `λ`. This is explanatory and not proved here.
- Compact sets of `λ` are expressed in linear coordinates, as in
  `Langlands.Analysis.Meromorphic.LinearCoordinates`, because
  `X^*(P) ⊗ ℂ` carries no chosen topology. The condition is required for
  every coordinate system; any two differ by a linear homeomorphism.

## Scope

Holomorphy of `λ ↦ E(g, φ, λ)` on the region, automorphy of `E`, its
growth, the precise region `Re λ ∈ ρ_P + 𝔞_P^{*+}` of MW II.1.5 and
Godement, and the meromorphic continuation (BL Theorem 2.3) are not part of
this statement.
