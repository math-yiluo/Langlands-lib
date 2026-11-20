# Twisted orbital integrals of a compact open subgroup’s characteristic function

This module states the orbital integral formula under a coset hypothesis and gives
algebraic reductions of that hypothesis for restricted products and cyclic shifts. The
three declarations are proposition definitions in `Langlands.TraceFormula`.

## `UnitTwistedOrbitalIntegralStatement`

Let `G : Type u` be a Hausdorff topological group with its Borel σ-algebra, let `μ` be
a left Haar measure (`μ.IsHaarMeasure`), and let `θ : G →* G` be continuous. Let `K`
be a compact open subgroup of `G` with `θ k ∈ K` for every `k ∈ K`, and fix `δ ∈ K`.

Put `C = twistedCentralizer θ δ`, the subgroup of elements `c` with
`c⁻¹ * δ * θ c = δ`. Equip the Library’s left quotient `LeftQuotient C = C \ G`, whose
classes are `C x` under left multiplication by `C`, with a Borel measurable structure.
Let `μC` be a measure on `C` with its induced Borel structure. Assume `μC` is right
invariant, finite on compact sets and positive on nonempty open sets. Let `ν` be a
measure on `C \ G`.

Assume `QuotientIntegration.IsCompatible C μ μC ν`. This means that `ν` is nonzero,
regular and invariant under right translation. For every continuous compactly supported
`f : G → ℂ`, the quotient average `C x ↦ ∫_C f(c x) dμC(c)` is `ν`-integrable and its
integral is `∫_G f dμ`.

Assume also that every `x : G` with `x⁻¹ * δ * θ x ∈ K` admits a factorization
`x = c * k` with `c ∈ C` and `k ∈ K`.

Write `1_K` for the complex-valued indicator `(K : Set G).indicator fun _ => (1 : ℂ)`.
The conclusion is that `twistedOrbitFunction θ δ 1_K`, given by
`C x ↦ 1_K (x⁻¹ * δ * θ x)`, is `ν`-integrable and that

```text
twistedOrbitalIntegral θ δ ν 1_K = (μ K).toReal / (μC (C ∩ K)).toReal
```

The right side is the real ratio viewed in `ℂ`. Here `C ∩ K` is a set in the subgroup
`C`, expressed by `Subtype.val ⁻¹' (K : Set G)`.

## `RestrictedProductTwistedCosetStatement`

Let `ι : Type w`, let `G i : Type u` be groups and let `K i` be subgroups of `G i`.
For each `i`, let `θ' i : G i →* G i` map `K i` into itself. On Mathlib’s restricted
product `Πʳ i, [G i, K i]` for the cofinite filter, let `θ` be a group endomorphism
such that `θ x i = θ' i (x i)` for every `x` and `i`. Fix an element `δ` of the
restricted product.

Suppose that for every `i`, each `y : G i` with `y⁻¹ * δ i * θ' i y ∈ K i` admits a
factorization `y = c * k` with `c ∈ twistedCentralizer (θ' i) (δ i)` and `k ∈ K i`.

Then every `x` in the restricted product satisfying `(x⁻¹ * δ * θ x) i ∈ K i` for
all `i` admits a factorization `x = c * k` in that group with
`c ∈ twistedCentralizer θ δ` and `k i ∈ K i` for all `i`.

## `SplitTwistedCosetStatement`

Let `H : Type u` be a group, `K` a subgroup of `H`, and `m` a natural number. Let `θ`
be a group endomorphism of `Fin (m + 1) → H` such that
`θ x = x ∘ finRotate (m + 1)` for every `x`. Thus `(θ x) i = x (i + 1)` with indices
modulo `m + 1`. Fix `δ : Fin (m + 1) → H` with `δ i ∈ K` for every `i`, and let
`N = (List.ofFn δ).prod` be the ordered product `δ 0 * δ 1 * ⋯ * δ m`.

Suppose that every `y : H` with `y⁻¹ * N * y ∈ K` admits a factorization `y = c * k`
with `c ∈ Subgroup.centralizer {N}` and `k ∈ K`.

Then every `x : Fin (m + 1) → H` with `(x⁻¹ * δ * θ x) i ∈ K` for all `i` admits a
factorization `x = c * k` with `c ∈ twistedCentralizer θ δ` and `k i ∈ K` for all `i`.

## Source and scope

These statements are derived from the unit calculation in Getz–Hahn, *An Introduction
to Automorphic Representations* (2024), §17.8, Lemma 17.8.3 and its proof (printed
p. 464, ending on p. 465). The source computes the normalized relative orbital
integral of the characteristic function of `X(O_{F_v})` at almost all places. Its proof
uses properness of the adelic orbit map (Theorem 17.7.1) and Exercise 17.15 (printed
p. 470) to obtain the local coset description after enlarging the finite set of places.
The twisted conjugation convention is the one in §18.5, (18.32) (printed p. 487).
[Getz–Hahn (2024)](https://link.springer.com/book/10.1007/978-3-031-41153-3)

- Statement 1 concerns one element of an arbitrary Hausdorff topological group. It
  takes the coset condition as a hypothesis and uses the Library’s left coset space
  with classes `C x`. Equation (18.32) uses the twisted conjugation integrand
  on an adelic quotient with split central groups removed.
- All three measures in statement 1 are explicit and retain their supplied scales.
  The formula specializes to `1` when both `μ(K)` and `μC(C ∩ K)` equal `1`.
  Integrability of the orbit function is part of the conclusion.
- Statements 2 and 3 use arbitrary groups and local coset premises. Statement 2
  handles the componentwise twist on a restricted product. Statement 3 models the
  cyclic shift at a split place through the ordered product `N`.
- The companion statement gives the ordinary coset property for `GL_n` over a
  discrete valuation ring under a unit-discriminant hypothesis on the characteristic
  polynomial. Its underlying local argument uses invariant lattices.
  [Unit discriminant cosets](UnitDiscriminantCosetStatement.md)
