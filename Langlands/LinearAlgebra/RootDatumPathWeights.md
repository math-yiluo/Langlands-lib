# Weights along a path component of type `A`

This module is an internal prerequisite for the quasi-split Steinberg quotient
task, specifically for the even type `A` case (Steinberg 1965, §9.10–9.19). It
uses no classification of Dynkin diagrams. Let `β 0, …, β (L - 1)` be a
connected component of type `A_L` of the Dynkin diagram, listed in path order,
and let `ω` be the fundamental weight at the end vertex `β 0`. The module
studies the weights

`ε_j = ω - (α_0 + ⋯ + α_{j-1})`, for `j = 0, …, L`,

where `α_i` is the root of `β i`. In the standard representation of
`SL_{L+1}` these are the weights of the standard basis vectors. The module proves
three facts.

- Simple reflections permute the `ε_j`.
- The `ε_j` are pairwise distinct.
- Let `S` be a set of weights that is stable under all simple reflections, and
  suppose every `ν ∈ S` lies below `ω`, meaning that `ω - ν` is a nonnegative
  integral combination of simple roots. Then every element of `S` is one of the
  `ε_j`. This is the statement that the fundamental weight `ω` is minuscule.

A companion module applies the last fact to the weights of an actual
highest-weight representation with highest weight `ω`. There these
are the weights of the first fundamental representation of the `A_{2m}`
factor, the representation used in Steinberg's even type `A` construction.

## Setting

All results are in the namespace `Langlands.LinearAlgebra.RootDatumPathWeights`.
`P : RootDatum ι M N` is a Mathlib root datum (a root pairing over `ℤ`), and
`M`, `N` are arbitrary additive commutative groups. The roots need not span
`M`, and `P` need not be reduced. `b : P.Base` is a base, `L : ℕ` and
`β : Fin L → b.support`. Write `⟨x, γ^∨⟩` for `P.toLinearMap x (P.coroot γ)`.
Only the final theorem requires `ι` to be finite. It needs `Finite ι` for the
canonical form `P.RootForm`.

## Definitions

- `IsPathComponent β`, a structure in `Prop`, has three fields. `pos` says
  `0 < L`. `pairing_eq` gives the pairings
  `P.pairing (β i) (β j)`: `2` if `i = j`, `-1` if `i + 1 = j` or
  `j + 1 = i`, and `0` otherwise. `isOrthogonal` says every simple root outside
  the range of `β` is orthogonal (`P.IsOrthogonal`) to every `β i`. So the range
  of `β` is a connected component of type `A_L`, listed in path order.
  `IsReversedPath.isPathComponent` shows that the reversed paths of
  `Langlands.LinearAlgebra.RootDatumReversedPath` are path components.
- `pathRoot β i` is `P.root (β i)` for `i < L` and `0` otherwise.
- `pathWeight β ω j = ω - Σ_{i < j} pathRoot β i`, which is `ε_j` above.
- `IsPathFundamental β ω`, a structure in `Prop`, says `ω` is the fundamental
  weight at `β 0`. The field `pairing_path` gives `⟨ω, (β i)^∨⟩ = 1` for
  `i = 0` and `0` otherwise. The field `pairing_off` gives `⟨ω, z^∨⟩ = 0` for
  every simple root `z` off the path. This is the Kronecker-delta condition of
  the Library's `SplitPinning.IsFundamentalWeight` at `β 0`, split into path and
  off-path coroots.

## Results

The results below assume `hβ : IsPathComponent β`, and those that mention `ω`
also assume `hω : IsPathFundamental β ω`.

- `IsPathComponent.injective`: `β` is injective. `pairing_mk`,
  `pairing_mk_left`, `pairing_succ_left` and `pairing_succ_right` restate the
  pairing pattern with indices given as natural numbers. Consecutive vertices
  have pairing `-1` in both orders.
- `pathWeight_zero`, `pathWeight_succ` and `pathRoot_of_lt` unfold the
  definitions: `ε_0 = ω` and `ε_{j+1} = ε_j - α_j`.
- `pairing_pathWeight` (and the variant `pairing_pathWeight_mk`): for `j ≤ L`
  and a path vertex `i`, `⟨ε_j, (β i)^∨⟩` is `1` if `j = i`, `-1` if
  `j = i + 1`, and `0` otherwise.
- `pairing_pathWeight_of_not_mem`: `⟨ε_j, z^∨⟩ = 0` for every simple root `z`
  off the path.
- `reflection_apply_eq`: Mathlib's reflection formula
  `s_γ x = x - ⟨x, γ^∨⟩ α_γ` in this notation.
- `reflection_pathWeight_self`: `s_{β j} ε_j = ε_{j+1}` for `j < L`.
- `reflection_pathWeight`: for every simple root `γ` and `j ≤ L`, `s_γ ε_j` is
  some `ε_{j'}` with `j' ≤ L`.
- `pathWeight_injOn`: `ε_j = ε_{j'}` with `j, j' ≤ L` implies `j = j'`.
- `exists_eq_pathWeight` (main result): let `ι` be finite and `S : Set M`. Assume
  `P.reflection γ ν ∈ S` for all `ν ∈ S` and simple `γ`, and
  `ω - ν ∈ AddSubmonoid.closure (range (fun γ : b.support => P.root γ))` for all
  `ν ∈ S`. Then every `ν ∈ S` equals `ε_j` for some `j ≤ L`. The closure is the
  same monoid as the Library's `SplitPinning.positiveRootMonoid`.

## Proof as implemented

**Pairings and reflections.** `pairing_pathWeight` is proved by induction on
`j`. The case `j = 0` is `hω.pairing_path`. The step subtracts the pairing
pattern of `α_j`, and an index case analysis (`split_ifs`, `omega`) gives
the formula. Off-path coroots pair to zero with `ω` and with every path root,
since off-path simple roots are orthogonal to the path. Then
`s_γ ε_j = ε_j - ⟨ε_j, γ^∨⟩ α_γ`. For `γ = β i` this is `ε_{i+1}` when
`j = i`, `ε_i` when `j = i + 1` (because `ε_{i+1} = ε_i - α_i`), and `ε_j`
otherwise. For `γ` off the path it is `ε_j`. Injectivity follows by pairing
with the coroot of `β j` for `j < j'`: the values are `1` and `-1` or `0`.

**Canonical form.** Private lemmas about `B = P.RootForm` (with a chosen
`Fintype ι`) give the following.

- `B` is symmetric and `B(x, x) ≥ 0`, since it is a sum of squares.
- `B(x, x) > 0` for nonzero `x` in the integral root span, by Mathlib's
  `disjoint_rootSpan_ker_rootForm`.
- `2 B(α_i, x) = ⟨x, α_i^∨⟩ B(α_i, α_i)` for every `x ∈ M`. Apply `x` to
  Mathlib's `rootForm_self_smul_coroot`.
- All path roots have the same norm `n = B(α_0, α_0)`, because consecutive path
  roots have pairing `-1` in both orders.
- For integer coefficients `x_i`, the norm of `Σ_{i < l} x_i α_i` (`l ≤ L`)
  satisfies `2 B = n · Q_l(x)`. Here
  `Q_l(x) = 2 Σ_{i<l} x_i² - 2 Σ_{1 ≤ i < l} x_{i-1} x_i` is the quadratic form
  of the Cartan matrix of type `A_l`. The proof is by induction on `l`. Only the
  previous vertex contributes to the cross term with `α_l`.
- `Q_L(x) ≥ x_0² + x_0` when `x_0 ≥ 0` and `L ≥ 1`. By induction,
  `Q_{l+1} - x_l² ≥ x_0² + |x_0| - |x_l|`. The step uses
  `Q_{l+2} - x_{l+1}² = (Q_{l+1} - x_l²) + (x_l - x_{l+1})²`,
  `|y| ≤ y²` for integers, and the triangle inequality.

**Dominant case** (`eq_of_dominant`). Let `ν` be dominant
(`⟨ν, γ^∨⟩ ≥ 0` for all simple `γ`) with `D = ω - ν = Σ_γ c_γ α_γ`, `c_γ ≥ 0`.
Then `2 B(D, ν) = Σ c_γ ⟨ν, γ^∨⟩ B(α_γ, α_γ) ≥ 0` and
`2 B(D, ω) = c_{β 0} n`, so `2 B(D, D) ≤ c_{β 0} n`. Split `D = D_A + D_R` into
its path part and its off-path part. They are `B`-orthogonal, and
`B(D_R, D_R) ≥ 0`. So `2 B(D, D) ≥ 2 B(D_A, D_A) = n Q_L ≥ n (c_{β 0}² + c_{β 0})`.
Hence `c_{β 0} = 0`, then `2 B(D, D) ≤ 0`, so `D = 0` and `ν = ω`.

**Induction** (`exists_eq_pathWeight`). Write `ω - ν = Σ c_γ α_γ` with
`c_γ ∈ ℕ` (`AddSubmonoid.mem_closure_range_iff_of_fintype`). The proof is by
induction on a bound for `Σ c_γ`. If `ν` is dominant, then `ν = ω = ε_0`.
Otherwise some `⟨ν, γ^∨⟩ = -k < 0`. The reflection `s_γ ν = ν + k α_γ` lies in
`S` and has coefficients `c' = c - k [· = γ]`. This follows from linear
independence of the base, comparing with the coefficients that `hle` gives
for `s_γ ν`. So its coefficient sum is smaller, and by induction `s_γ ν = ε_j`.
Then `ν = s_γ (s_γ ν) = s_γ ε_j` is again a path weight by
`reflection_pathWeight`.

## Scope

The module is pure root-datum combinatorics. It does not mention group schemes
or representations, and it constructs no fundamental weight. Its results apply
to a weight `ω` that is supplied together with `IsPathFundamental β ω`.
