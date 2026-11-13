# Waldspurger's constant `c(G|M)` on actual rational points

Worker 5. This module defines the constant `c(G|M)` of J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), I.1, printed p.241 /
PDF p.7. There, for a semi-standard parabolic `P = MU` and
`α ∈ Σ_red(P)`, `A_α` is the neutral component of `ker α` in `A_M`,
`M_α = Z_G(A_α)` is a semi-standard Levi subgroup, and

`c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)`.

Here `γ(G|M) = γ(P)` is the constant in formula (2) of I.1 (p.240), and
Remark (3) states that, for the special maximal compact subgroup `K`
fixed on p.240, it depends only on `M` and not on the parabolic `P`. The same product of the
`γ(M_α|M)`, squared, is the factor in the Plancherel density
`μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²` of V.2 (printed p.292 / PDF p.58). There `α`
runs over the reduced roots of `A_M` up to sign. This module does not
define `μ`.

The definitions are derived. The Lean objects encode Waldspurger's
`A_α`, `M_α` and `γ(M_α|M)` through cocharacter submodules and the
Library's dynamic subgroups, as explained below. This module proves that
the definitions are well formed and proves elementary bounds. It does not
prove that they agree with Waldspurger's objects (see "Not proved here").

## Setting

`F` is a nonarchimedean local field in any universe. `G` is an affine
group scheme over `F`, locally of finite type. Reductivity is not assumed
by the definitions. The rational points `G(F)` carry the Library's
rational-point topology and Borel σ-algebra. `T` is a commutative group
scheme with a homomorphism `i : T → G` (in the intended application, a
maximal split torus). `ζ` is a cocharacter of `T`, and
`χ = ζ ≫ i : G_m → G`. The parabolic is `P = P_G(χ)`, its Levi is
`M = Z_G(χ)`, and the opposite radical is `Ū = U_G(χ⁻¹)`. These are the
Library's dynamic subgroups (`Dynamic.parabolic`, `Dynamic.centralizer`,
`unipotentPoints (oppositeCocharacter χ)`). `K` is a compact open subgroup
of `G(F)`. All Haar measures are the Library's
`Haar.subgroupCompactOpenHaar K hK`, so each closed subgroup `H` gets
`mes(H ∩ K) = 1`. This is Waldspurger's normalization (I.1, p.240) for the
supplied `K`.

## Generic lower bound

`one_le_compactNormalizedSourceGamma`: for closed subgroups `P` and `V` of
a topological group `A` with compact open subgroup `K`, the Library's
`compactNormalizedSourceGamma` satisfies `1 ≤ γ`. This constant is
`∫_V ∫_P 1_K(p v⁻¹) dp dv`. The proof bounds the integrand from below by
`1_{P ∩ K}(p) 1_{V ∩ K}(v)`, because `p v⁻¹ ∈ K` whenever `p ∈ K` and
`v ∈ K`. Both normalized masses are `1`.

## Algebraic part (any field `k`)

- `cocharacterSubmoduleCentralizer i N`, for an integer submodule `N` of
  `X_*(T)`, is the subgroup functor of `G` given by the intersection of
  the dynamic centralizers `Dynamic.centralizer (ν ≫ i)` over `ν ∈ N`.
  It is the centralizer of the cocharacters in `N`.
  `mem_cocharacterSubmoduleCentralizer` unfolds membership.
- `cocharacterSubmoduleCentralizer_cocharacterAnnihilator`: on the
  Library's annihilator submodule `cocharacterAnnihilator T J`, this
  centralizer equals the Library's `cocharacterAnnihilatorCentralizer i J`.
- `groupHom_zsmul_comp`: the cocharacter `n • ζ` followed by `i` equals
  the `n`-th power map of `G_m` followed by `ζ ≫ i`. The proof uses
  `Gm.powerHom_apply` and `Preadditive.zsmul_comp`.
- `leviRelativeRoots i ζ` is the set of relative roots `α` of `T` (the
  Library's `relativeRoots i`) with `⟨α, ζ⟩ = 0`. These are the roots of
  `T` in `M`.
- `rankOneCocharacters i ζ β` is `cocharacterAnnihilator T (insert β
  (leviRelativeRoots i ζ))`: the cocharacters of `T` killed by `β` and by
  every root of `M`.
- `rankOneCocharacterSet i ζ` is the image of `positiveRelativeRoots i ζ`
  (roots with `⟨β, ζ⟩ > 0`) under `rankOneCocharacters i ζ`. This set
  indexes the product in `c(G|M)`.
- `cocharacterSubmoduleCentralizer_rankOneCocharacters` rewrites the
  centralizer of `rankOneCocharacters i ζ β` as
  `cocharacterAnnihilatorCentralizer i (insert β (leviRelativeRoots i ζ))`.
- `finite_rankOneCocharacterSet` shows the index set is finite when
  `relativeRoots i` is finite. `finite_rankOneCocharacterSet_of_isSplitTorus`
  gets finiteness for a split torus `T` from the Library's
  `IsSplitTorus.finite_relativeRoots` (needs `G` locally of finite type).
- `leviRelativeRoots_zsmul`, `positiveRelativeRoots_zsmul` and
  `rankOneCocharacterSet_zsmul`: these sets do not change when `ζ` is
  replaced by `n • ζ` with `n > 0`.

### Relation to Waldspurger's index set

Take `T` to be the maximal split torus `A_0`, `i` its inclusion, and `ζ`
such that `P = P_G(ζ ≫ i)` and `M = Z_G(ζ ≫ i)`. Then:

- `X_*(A_M)` is the annihilator of the roots of `M`.
- For a root `β` of `T` with `⟨β, ζ⟩ > 0`, its restriction `α` to `A_M`
  is a root of `A_M` in `U`, and `X_*(A_α) = {ν ∈ X_*(A_M) : ⟨β, ν⟩ = 0}`.
  This is `rankOneCocharacters i ζ β`.
- Proportional roots of `A_M` have the same `A_α`, and non-proportional
  roots have different `A_α`. By the next point, `α ↦ X_*(A_α)` is
  therefore a bijection from `Σ_red(P)` onto `rankOneCocharacterSet i ζ`.
- `Σ_red(P)` consists of the reduced roots: on each ray of positive
  proportional roots only the shortest is reduced. So distinct elements
  of `Σ_red(P)` are not proportional.
- `A_α` is a split torus, so a point centralizes `A_α` exactly when it
  centralizes the images of all cocharacters of `A_α`. Hence
  `M_α = Z_G(A_α)` is `cocharacterSubmoduleCentralizer i (X_*(A_α))`.

These identifications are standard structure theory. They are the
intended reading of the definitions and are **not** proved in Lean.

Indexing by submodules rather than by roots means no choice of reduced
representative is needed. Each `α ∈ Σ_red(P)` contributes exactly one
factor, even when several roots `β` of `T` restrict to `α` or to its
multiples.

## Rational points (nonarchimedean local `F`)

- `isClosed_parabolic_inf` and `isClosed_oppositeRadical_inf`: for a
  closed subgroup `L` of `G(F)`, the subgroups `P(F) ∩ L` and `Ū(F) ∩ L`
  are closed. This uses the Library's closedness of the dynamic parabolic
  and radical.
- `leviGamma χ K hK L hL` is the Library's `compactNormalizedSourceGamma`
  of the closed subgroups `P(F) ∩ L` and `Ū(F) ∩ L`. Each is normalized by
  `mes(· ∩ K) = 1`. Concretely it is `∫_{Ū∩L} ∫_{P∩L} 1_K(p v⁻¹) dp dv`.
  Since `p v⁻¹ ∈ L`, this equals the same open-cell constant computed
  inside `L` with `K ∩ L`, which Waldspurger normalizes by
  `mes(H ∩ K) = 1` for subgroups of `L` as well. For `L = M_α(F)` this is
  the Library's `gamma` construction for the parabolic `P ∩ M_α` of
  `M_α`, whose Levi is `M` and whose opposite radical is `Ū ∩ M_α`. It is
  therefore the intended `γ(M_α|M)` (see "Not proved here").
- `leviGamma_eq_gamma_of_le`: if `P(F) ≤ L` and `Ū(F) ≤ L`, then
  `leviGamma` equals the Library's `gamma χ K hK`. The proof is
  `compactNormalizedSourceGamma_eq_of_transport` along the identity, with
  `P ∩ L = P` and `Ū ∩ L = Ū`. `leviGamma_top` is the case `L = ⊤`.
- `one_le_leviGamma` and `one_le_gamma` give `1 ≤ γ` from the generic
  bound.
- `leviGamma_precomp_power`: replacing `χ` by a positive power leaves
  `leviGamma` unchanged. The proof uses the Library's
  `Dynamic.parabolic_precomp_power`, `oppositeCocharacter_precomp_power`
  and `Dynamic.unipotent_precomp_power`.
- `isClosed_cocharacterSubmoduleCentralizer`: the rational points of
  `cocharacterSubmoduleCentralizer i N` form a closed subgroup. They are
  an intersection of rational points of dynamic centralizers, which are
  closed by the Library's `isClosed_levi`. This holds for every `N`, so
  no Levi hypothesis is needed to define the factors.
- `rankOneGamma i ζ K hK N` is `leviGamma (ζ ≫ i) K hK L _` for
  `L = (cocharacterSubmoduleCentralizer i N)(F)`. For
  `N = X_*(A_α)` this is the intended `γ(M_α|M)`.
- `rankOneGammaProduct i ζ K hK` is the finite product (`finprod`)
  `∏ᶠ N ∈ rankOneCocharacterSet i ζ, rankOneGamma i ζ K hK N`.
- **`plancherelConstant i ζ K hK`** is
  `(gamma (ζ ≫ i) K hK)⁻¹ * rankOneGammaProduct i ζ K hK` in `ℝ≥0∞`. This
  is Waldspurger's `c(G|M)`. `plancherelConstantReal` is its real value.

Mathlib's `finprod` is the product of the factors different from `1`
when there are finitely many such factors, and it is `1` when infinitely
many factors differ from `1`. For a split `T`, or whenever
`relativeRoots i` is finite, the index set is finite, and
`rankOneGammaProduct_eq_prod` and
`rankOneGammaProduct_eq_prod_of_isSplitTorus` rewrite the product as the
`Finset` product over the index set, so no factor is lost.

### Proved properties

- `one_le_rankOneGamma` and `one_le_rankOneGammaProduct`: every factor,
  and the product, is at least `1`. The product bound uses
  `finprod_mem_induction`.
- `rankOneGammaProduct_ne_top` and `plancherelConstant_ne_top`: if every
  factor indexed by the set is finite, then the product and `c(G|M)` are
  finite. The bound uses `γ(G|M) ≥ 1`, so `γ(G|M)⁻¹` is finite.
- `plancherelConstant_ne_zero` holds when `γ(G|M) ≠ ⊤`. For `G` smooth,
  `plancherelConstant_ne_zero_of_smooth` gets this from the Library's
  `gamma_ne_zero_ne_top_of_smooth`.
- `plancherelConstantReal_pos_of_smooth`: for smooth `G`, if all factors
  are finite then `0 < c(G|M)`.
- `plancherelConstant_le_rankOneGammaProduct`: `c(G|M) ≤ ∏ γ(M_α|M)`,
  since `γ(G|M)⁻¹ ≤ 1`.
- `rankOneGamma_zsmul`, `rankOneGammaProduct_zsmul` and
  `plancherelConstant_zsmul`: each object is unchanged when `ζ` is
  replaced by `n • ζ` with `n > 0`. The proofs use `groupHom_zsmul_comp`,
  `leviGamma_precomp_power`, `rankOneCocharacterSet_zsmul` and the
  Library's `gamma_precomp_power`.

## Not proved here

- The identification of `rankOneCocharacterSet`,
  `cocharacterSubmoduleCentralizer` and `rankOneGamma` with Waldspurger's
  `Σ_red(P)`, `M_α` and `γ(M_α|M)` described above. In particular, this
  module does not show that `M_α` is a Levi subgroup or that `P ∩ M_α` is
  a parabolic subgroup of `M_α` with Levi `M`.
- Finiteness of `γ(M_α|M)`. This needs `M_α` as a smooth group scheme
  with its open cell, which is not built here. Finiteness is therefore a
  displayed hypothesis of `plancherelConstant_ne_top`.
- Remark (3): for the fixed special maximal compact subgroup `K`,
  independence of `γ(G|M)` and `γ(M_α|M)` from the choice of the
  parabolic `P` with Levi `M`. The constants here depend on `ζ` and on the
  supplied `K`. The only proved independence is from positive multiples
  of `ζ`, with `K` unchanged. Waldspurger fixes `K` once and for all, and
  this module makes no claim about changing `K`.
- The existence of Waldspurger's special maximal compact subgroup and its
  factorization properties.
- The density `μ(ω)` of V.2 and any Plancherel identity.
