# The algebra with orthogonal involution descended along a similitude cocycle

Author: Worker 1383, for Task 6507 (`f0045927-f50c-4853-9944-3c98c7ea5daf`), in collaboration
with Worker 74. This module is the orthogonal counterpart of
`SymplecticInnerForm/TwistedAction`. It uses the general semilinear Galois descent of
`SpecialLinearInnerForm/GaloisDescent` (`SemilinearGaloisAction`, its fixed algebra, `trace`
and `descentEquiv`), `SemilinearGaloisAction.fixedInvolution` from
`SymplecticInnerForm/GaloisInvolution`, and the matrix facts of the module
`EvenOrthogonalForm/Similitude` (Worker 74).

## Setting

All declarations are in the namespace `Langlands.GroupScheme.EvenOrthogonalForm`. Fix fields
`K` and `N` with `N` a `K`-algebra (universe `u`), a natural number `n`, and a family
`g : Gal(N/K) → GL_{2n}(N)`, written `(N ≃ₐ[K] N) → GL (Fin n ⊕ Fin n) N`. Matrices are indexed
by `Fin n ⊕ Fin n`. For a matrix `x` and `γ ∈ Gal(N/K)`, `γ(x)` is `x.map γ` (apply `γ` to every
entry). Notation from `Similitude`: `Q = formMatrix (Fin n) N = [[0, 1], [0, 0]]`,
`J = polarMatrix (Fin n) N = [[0, 1], [1, 0]]`, `p = leftProjection N (Fin n) = [[1, 0], [0, 0]]`,
and `τ₀ = orthogonalInvolution N (Fin n)`, the involution `x ↦ J xᵀ J`. `Alt τ₀` is its
alternating subspace `{y - τ₀ y}`.

## The twisted action

- `twistMatrix g γ x = g_γ⁻¹ γ(x) g_γ`.
- `map_galois_mul`: `γ(xy) = γ(x) γ(y)`.
- `mul_twistMatrix_mul`: `g_γ (twistMatrix g γ x) g_γ⁻¹ = γ(x)`. Hence `twistMatrix_injective`.
- `twistRingHom g γ` is `twistMatrix g γ` as a ring endomorphism of `M_{2n}(N)`, with
  `twistRingHom_apply` (by `rfl`). `twistMatrix_algebraMap`: it sends the scalar matrix `c · 1`
  to `γ(c) · 1`, because scalar matrices are central.
- The hypothesis `hcoc : ∀ γ δ x, twistMatrix g γ (twistMatrix g δ x) = twistMatrix g (γ * δ) x`
  says that the twisted maps compose like the Galois group.
- `twistedAction g hcoc : SemilinearGaloisAction K N (M_{2n}(N))` has action `twistRingHom g`.
  The composition law is `hcoc`. The identity law follows from `hcoc 1 1 x` and
  injectivity of `twistMatrix g 1`. `twistedAction_act` (by `rfl`) gives the action.
- `map_galois_fixed`: an element `a` of the fixed algebra satisfies `γ(a) = g_γ a g_γ⁻¹`. This
  is `mul_twistMatrix_mul` together with `θ_γ(a) = a`.

Assume now that `N/K` is finite and Galois. The instances `FiniteDimensional K fixed`,
`Algebra.IsCentral K fixed` and `IsSimpleRing fixed` come from the general descent theorems
`finiteDimensional_fixed`, `isCentral_fixed` and `isSimpleRing_fixed`. The last two require
`NeZero n`, so that the matrix algebra is nonzero.

## The descended involution

The hypothesis `hsim : ∀ γ, ∃ μ : Nˣ, IsAlt (g_γ Q g_γᵀ - μ Q)` says that every `g_γ` is a
similitude of the split hyperbolic quadratic form.

- `twistMatrix_orthogonalInvolution hsim γ x`: `θ_γ (τ₀ x) = τ₀ (θ_γ x)`. Entrywise `γ` commutes
  with `τ₀` (`orthogonalInvolution_map`). Conjugation by `g_γ` commutes with `τ₀` by
  `orthogonalInvolution_conj_of_similitude`, applied with the polar identity
  `g_γ J g_γᵀ = μ J` (`similitude_polar`).
- `descendedInvolution g hcoc hsim : FirstKindInvolution K fixed` is the restriction of `τ₀` to
  the fixed algebra (`fixedInvolution`). By `coe_descendedInvolution` (by `rfl`), its value on
  `a` is `τ₀ a`.
- `descentEquiv_descendedInvolution`: through the descent chart
  `descentEquiv : N ⊗[K] fixed ≃ₐ[N] M_{2n}(N)`, the extended involution `τ_N` becomes `τ₀`.
  This is the general `descentEquiv_fixedInvolution`.
- `descentEquiv_descendedInvolution_mul_polar`: equivalently,
  `descentEquiv (τ_N x) * J = J * (descentEquiv x)ᵀ` (`orthogonalInvolution_mul_polar`). This is
  the compatibility hypothesis `he` of `OrthogonalInnerForm.orthogonalInvolutionHermitian` for the
  chart `descentEquiv`.

## The base point

- `exists_trace_eq_one K N`: some `c ∈ N` has `Tr_{N/K}(c) = 1`. The trace form of the
  separable extension `N/K` is nonzero (`Algebra.trace_ne_zero`), and dividing an element of
  nonzero trace by its trace gives `c`. `traceOneElement K N` is a chosen such `c`, and
  `sum_galois_traceOneElement`: `∑_γ γ(c) = 1` (`trace_eq_sum_automorphisms`).
- `basePoint g hcoc = ∑_γ θ_γ(c p)`, the descent `trace` of `c p`, an element of the fixed
  algebra. By `twistMatrix_smul` (`θ_γ(c x) = γ(c) θ_γ(x)`), `coe_basePoint` gives
  `basePoint = ∑_γ γ(c) θ_γ(p)` as a matrix.
- `twistMatrix_leftProjection_sub_mem hsim γ`: `θ_γ(p) - p ∈ Alt τ₀`. Here `γ(p) = p`, and
  conjugation by a similitude moves `p` by an alternating element
  (`conj_leftProjection_sub_mem`).
- `basePoint_sub_mem`: `basePoint - p ∈ Alt τ₀`. Since `∑_γ γ(c) = 1`,
  `basePoint - p = ∑_γ γ(c) (θ_γ(p) - p)`, a sum of elements of the subspace `Alt τ₀`.
- `basePoint_add_descendedInvolution`: `a₀ + τ a₀ = 1` for `a₀ = basePoint g hcoc` and
  `τ = descendedInvolution g hcoc hsim`. For each `γ`, since `θ_γ` commutes with `τ₀` and
  `p + τ₀ p = 1` (`leftProjection_add_orthogonalInvolution`),
  `γ(c) θ_γ(p) + τ₀(γ(c) θ_γ(p)) = γ(c) θ_γ(p + τ₀ p) = γ(c) · 1`. Summing over `γ` gives
  `(∑_γ γ(c)) · 1 = 1`.

No hypothesis on the characteristic of `K` is used.

## Provenance

Derived. The fixed algebra is the twist of the split algebra with involution
`(M_{2n}(N), τ₀)` by the cocycle `γ ↦ Int(g_γ)` with values in the projective similitudes,
as in M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (AMS
Colloquium Publications 44, 1998; source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`), §29.F, printed pp.408–409 /
PDF pp.431–432, and Proposition (26.2), printed pp.361–362 / PDF pp.384–385. Here the twist is
made concrete as the fixed algebra of the semilinear action `θ`. The base point `a₀` is the
descended form of the projection `p`. The pair `(τ₀, [p])` is the quadratic pair of the split
hyperbolic form (KMRT §5.B). An element `ℓ` with `ℓ + σ(ℓ) = 1`, as in KMRT Proposition (5.7)
(printed p.56 / PDF p.79), is obtained here by Galois averaging with an element of trace one.
`a₀` is then the element that defines the isometry group scheme `IsometryCut.groupScheme` of
`(A, τ, a₀)` (Library module `Quaternionic/IsometryCut`), used in the module `SplitChart`. The
proofs above are direct computations. They follow the pattern of the symplectic module
`SymplecticInnerForm/TwistedAction`.
