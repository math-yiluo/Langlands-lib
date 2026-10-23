# The explicit ordinary cochain cup and its Leibniz identity

This module works in namespace `Langlands.Tate`. It fixes a commutative ring
`R`, a group `G`, and representations `A`, `B`, `C` in `Rep R G`, all in
one arbitrary universe `u`. It uses
`φ : Pairing A B C` from the published `ZeroDefinitions` module. This is an
`R`-bilinear map `φ.bilinear : A →ₗ[R] B →ₗ[R] C` with the equivariance law
`φ.bilinear (g • a) (g • b) = g • φ.bilinear a b`. The module makes no
finiteness assumption on `G` and no flatness assumption.

The cochains are Mathlib's actual inhomogeneous cochains
`(groupCohomology.inhomogeneousCochains A).X n`, which are functions
`(Fin n → G) → A`. The differential is Mathlib's root-namespace
`inhomogeneousCochains.d`:

```text
d f (g₀, …, gₙ) = g₀ • f (g₁, …, gₙ)
                  + Σ_{j = 0}^{n} (-1)^(j+1) f (contractNth j (g₀, …, gₙ)).
```

Here `contractNth j` multiplies the adjacent entries `gⱼ gⱼ₊₁` when `j < n`.
For `j = n` it drops the last entry.

## Definition

`ordinaryCochainCup φ p q` is an `R`-bilinear map

```text
(inhomogeneousCochains A).X p →ₗ[R] (inhomogeneousCochains B).X q →ₗ[R]
  (inhomogeneousCochains C).X (p + q).
```

It is built with `LinearMap.mk₂`. The four bilinearity side conditions follow
pointwise from the linearity of `f`, `g`, `B.ρ` and `φ.bilinear`.
`ordinaryCochainCup_apply`, proved by `rfl`, gives its value on a tuple
`s : Fin (p + q) → G`:

```text
ordinaryCochainCup φ p q f g s =
  φ.bilinear (f (fun i => s (Fin.castAdd q i)))
    (B.ρ ((List.ofFn (fun i : Fin p => s (Fin.castAdd q i))).prod)
      (g (fun j => s (Fin.natAdd p j)))).
```

In classical notation this reads
`(f ∪ g)(s₁, …, sₚ₊q) = φ(f(s₁, …, sₚ), (s₁ ⋯ sₚ) · g(sₚ₊₁, …, sₚ₊q))`.
The first `p` entries go to `f` and the last `q` entries go to `g`. The
prefix product is taken in increasing index order. For `p = 0` it is the
empty product `1`, so `B.ρ 1` acts as the identity.

## Leibniz identity

`ordinaryCochainCup_d` states, for all `f` in degree `p` and `g` in
degree `q`:

```text
inhomogeneousCochains.d C (p + q) (ordinaryCochainCup φ p q f g) =
  OrdinaryCup.transport C (_ : (p + 1) + q = (p + q) + 1)
      (ordinaryCochainCup φ (p + 1) q (inhomogeneousCochains.d A p f) g)
  + (-1 : R) ^ p • ordinaryCochainCup φ p (q + 1) f
      (inhomogeneousCochains.d B q g).
```

`OrdinaryCup.transport` is the published degree-transport equivalence from
`OrdinaryCupLeibniz`. By `OrdinaryCup.transport_apply`, it acts as
precomposition with `Fin.cast`. The second summand has degree `p + (q + 1)`,
which is definitionally `(p + q) + 1`, so it needs no transport. This
statement has exactly the form of the `leibniz` hypothesis of
`OrdinaryCup.fromLeibniz` for `cp := ordinaryCochainCup φ`. The descent to
`groupCohomology` is not part of this module.

## Proof

The proof evaluates both sides at `x : Fin (p + q + 1) → G`. It unfolds the
cup, the three differentials and `transport_apply`.

1. **Leading terms.** On the left, the leading term is
   `x₀ • (f ∪ g)(x₁, …, xₚ₊q)`. On the right, the leading term of `df` gives
   `φ(x₀ • f(x₁, …, xₚ), (x₀ x₁ ⋯ xₚ) • g(xₚ₊₁, …, xₚ₊q))`. Write the prefix
   product as `x₀` times `x₁ ⋯ xₚ`, using `List.ofFn_succ`. Equivariance
   `φ.equivariant` then identifies the two leading terms.
2. **Splitting the sum.** The sum on the left runs over `Fin (p + q + 1)`. It
   is split by `Fin.sum_univ_add` into indices `castAdd (q + 1) i` with
   `i < p` and indices `natAdd p k` with `k ≤ q`. The sum of `df` is split by
   `Fin.sum_univ_castSucc` into its interior terms and its last term.
3. **Tuple lemmas.** Private lemmas describe `Fin.contractNth` on each block.
   - For an interior index `castAdd (q + 1) i`, the front block is the
     contraction of `(x₀, …, xₚ)` at `i.castSucc`. The back block is
     `(xₚ₊₁, …, xₚ₊q)`.
   - For an index `natAdd p k`, the front block is `(x₀, …, xₚ₋₁)`. The back
     block is the contraction of `(xₚ, …, xₚ₊q)` at `k`.
   - Contracting `(x₀, …, xₚ)` at its last index drops `xₚ`.
   - Contracting an interior adjacent pair does not change the ordered
     product. This follows from `Fin.partialProd_contractNth` at the last
     index.
4. **Matching.** The interior terms of the left sum equal the interior terms
   of `df ∪ g`, with the same sign `(-1)^(i+1)`. The product of
   `(x₀, …, xₚ)` splits off its last factor `xₚ` (`List.ofFn_succ'`). So the
   last term of `df ∪ g` has sign `(-1)^(p+1)`. It cancels the leading term
   of `(-1)^p • (f ∪ dg)`. The terms with index `natAdd p k` equal
   `(-1)^p` times the sum terms of `f ∪ dg`, since
   `(-1)^(p+k+1) = (-1)^p (-1)^(k+1)`.
5. After one `simp only` normalization with these facts, the `module` tactic
   closes the remaining identity in the `R`-module `C`.

## Provenance and scope

The convention comes from the standard-complex diagonal in Cartan–Eilenberg,
*Homological Algebra* (1956), XI §7, p. 221 (PDF p. 243). That page displays
`j[x₁, …, xₙ] = Σ_{0 ≤ p ≤ n} [x₁, …, xₚ] ε(xₚ₊₁ ⋯ xₙ) ⊗ x₁ ⋯ xₚ [xₚ₊₁, …, xₙ]`
and states that the formula is also valid for unnormalized standard
complexes. With the unit augmentation `ε = 1`, its component of bidegree
`(p, q)` is `[s₁, …, sₚ] ⊗ (s₁ ⋯ sₚ)[sₚ₊₁, …, sₚ₊q]`. Evaluate equivariant
cochains on this component and apply the equivariant pairing. This gives
`φ(f(s₁, …, sₚ), (s₁ ⋯ sₚ) · g(sₚ₊₁, …, sₚ₊q))`, with the prefix product in
increasing order. This last step is our own derivation from the displayed
diagonal; that page does not print a cochain formula.

Cartan–Eilenberg XII §4, p. 242 (PDF p. 264), displays the cochain rule
`d(f·g) = (df)·g + (-1)^p f·(dg)`. That chapter concerns complete resolutions
of finite groups. It is used here only as a sign convention.

Serre, *Local Fields* (1979), VII §3, pp. 112–113 (PDF pp. 118–119), formula
(**), fixes the left-action inhomogeneous differential that Mathlib uses. It
has the leading action term, adjacent products with alternating signs, and
the final omission term. Serre VIII §3, pp. 131–132 (PDF pp. 137–138), gives
the equivariant-pairing convention `φ(sa, sb) = s φ(a, b)`, but does not
display this tuple formula.

The Lean construction and the direct finite-sum Leibniz calculation above
are internal derivations. They work over an arbitrary commutative ring and an
arbitrary group. No finite-group Tate result is assumed as a cochain
identity. Worker 210 checked the cited pages against the original PDFs.

This module does not define the cohomology operation `ordinaryCup`. It proves
no descent to `groupCohomology` and no comparison with the Tate cup. It
proves no associativity, commutativity or naturality law.
