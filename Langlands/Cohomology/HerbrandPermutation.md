# Herbrand quotients of permutation lattices

Let a finite cyclic group `G` act on a finite set `X`, and let `ℤ[X]` be the permutation
representation. This module proves that

- `H¹(G, ℤ[X]) = 0`;
- `|H²(G, ℤ[X])| = ∏_O |G_O|`, with one factor for each orbit `O`, where `G_O` is the
  stabilizer of any point of `O`.

In particular the Herbrand quotient of `ℤ[X]` is `∏_O |G_O|`. Both cohomology groups are
Mathlib's ordinary `groupCohomology`. `ℤ[X]` is Mathlib's `Rep.ofMulAction (ULift ℤ) G X` over
the lifted integers `ULift.{u} ℤ`, which are the Library's
`NormalizedTwoCocycle.CoefficientScalars.{u}`.

This is infrastructure for the first fundamental inequality in global class field theory
(task fb66219f). With `X` the infinite places of `E` and `G = Gal(E/F)`, it gives the
permutation-lattice formula `CyclicInfinitePlaceLatticeHerbrandQuotient`, the target of proof
task 9a181ede. That proposition is not proved in this module. A private compile test derived
it from `hasHerbrandQuotient_ofMulAction` in a few lines; `archimedeanHerbrandFactor F E` is
definitionally `orbitStabilizerProduct (E ≃ₐ[F] E) (InfinitePlace E)`.

All declarations are in the namespace `Langlands.Cohomology.Herbrand`. The module builds on
`Langlands.Cohomology.HerbrandQuotient`, which supplies `HasHerbrandQuotient`, the
identifications `H¹ ≅ ker N ⧸ range (ρ(g) - 1)` and `H² ≅ ker (ρ(g) - 1) ⧸ range N` for a
generator `g`, and `nonempty_linearEquiv_subquotient`.

## Mathematical content and source

Milne, *Class Field Theory* v4.03, Chapter VII, proof of Proposition 3.1, printed p.209
(PDF p.218), considers `N = Hom(T, ℤ)`, the integer permutation lattice on a finite `G`-set
`T`. It decomposes `N` into orbits `Hom(G/G_v, ℤ) = Ind_{G_v}^G ℤ` and uses Shapiro's lemma and
`h(G_v, ℤ) = n_v` to get

  `h(G, N) = ∏_v h(G_v, ℤ) = ∏_v n_v`.

**The route of the Lean proof.** It does not use Shapiro's lemma or the orbit decomposition.
Instead it computes the two subquotients directly. Fix a generator `g` of `G` and write
`N = Σ_σ ρ(σ)` for the norm. For each orbit `q`, let `orbitSum q : ℤ[X] → ℤ` be the sum of the
coordinates over `q`. It is invariant under `G`, so `orbitSum q (N x) = |G| · orbitSum q x`.

1. **`H¹ = 0`.** If `N x = 0` then every orbit sum of `x` vanishes. For a point `y` in the
   orbit of a chosen representative `b`, write `y = g^n b`. The telescoping sum
   `δ_{g^n b} - δ_b = (ρ(g) - 1)(δ_{g^{n-1} b} + ⋯ + δ_b)` lies in `range (ρ(g) - 1)`. Hence
   `x = Σ_y x_y (δ_y - δ_{b(y)}) + Σ_q (orbitSum q x) δ_{b_q}` lies in `range (ρ(g) - 1)`, since
   the second sum is zero. So `ker N ⧸ range (ρ(g) - 1) = 0`.
2. **`|H²| = ∏ |G_O|`.** An element of `ker (ρ(g) - 1)` is fixed by all of `G`, hence constant
   on each orbit. For such `x`, `orbitSum q x = |O_q| · x(b_q)`. Map `x` to the family of
   residues `(x(b_q) mod |G_{b_q}|)_q`. This map is surjective onto `∏_q ℤ/|G_{b_q}|`, using
   invariant elements that are constant on each orbit. Its kernel is `range N`, by the
   orbit-stabilizer theorem `|O_q| · |G_{b_q}| = |G|`:
   - if `x = N z`, then `|O_q| x(b_q) = |G| orbitSum q z`, so `x(b_q) = |G_{b_q}| orbitSum q z`;
   - conversely, if `x(b_q) = |G_{b_q}| m_q` for all `q`, then `x = N(Σ_q m_q δ_{b_q})`. Both
     sides are invariant and have the same orbit sums, and an invariant element is determined
     by its orbit sums.

   Hence `ker (ρ(g) - 1) ⧸ range N ≅ ∏_q ℤ/|G_q|`.

Provenance: derived. The result is the permutation-lattice computation in Milne's proof of
Proposition 3.1. The direct orbit-sum computation replaces Shapiro's lemma, and the following
are internal: `orbitSum`, the stabilizer-order bookkeeping `orbitStabilizerOrder` and
`orbitStabilizerProduct`, and the residue map.

## Conventions and scope

- `G : Type u` is a group and `X : Type u` carries a `MulAction G X`. The representation is
  `Rep.ofMulAction (ULift.{u} ℤ) G X`, whose elements are `MonoidAlgebra (ULift ℤ) X`, with
  `ρ(σ)(δ_x) = δ_{σx}`. In coordinates this is `(ρ(σ) f)(x) = f(σ⁻¹x)`; see
  `Representation.coeff_ofMulAction`.
- The cohomological theorems assume `[Finite G] [IsCyclic G] [Finite X]`. The trivial group,
  trivial actions and empty `X` are allowed; for empty `X` the product is empty, equal to `1`.
- Orbits are `Quotient (MulAction.orbitRel G X)`. The stabilizer order of an orbit is
  `Quotient.lift` of `Nat.card (MulAction.stabilizer G x)`. It is well defined because
  stabilizers of points in one orbit are isomorphic (`stabilizerEquivStabilizerOfOrbitRel`).
  This is the same construction as the Library's `infiniteOrbitStabilizerOrder`.

## Declarations

### `Orbits` (any group acting on any type)

- `orbitStabilizerOrder G X : Quotient (orbitRel G X) → ℕ` (def): the order of the
  stabilizer, as a function on orbits. `orbitStabilizerOrder_mk` gives its value at the orbit
  of `x`, and `orbitStabilizerOrder_pos` shows that it is positive for finite `G`.
- `orbitStabilizerProduct G X : ℕ` (def): the product of `orbitStabilizerOrder` over all
  orbits, given finitely many orbits. `orbitStabilizerProduct_pos` shows that it is positive.

### `Permutation`

- `orbitSum q : MonoidAlgebra (ULift ℤ) X →+ ℤ` (def, for `[Fintype X]`): the sum of the
  integer coordinates over the orbit `q`.
  - `orbitSum_apply` unfolds it.
  - `orbitSum_single`: its value on `δ_y` scaled by `r`.
  - `orbitSum_ofMulAction`: it is invariant under `ρ(σ)`.
  - `orbitSum_norm`: `orbitSum q (N x) = |G| · orbitSum q x`.
- `mk_smul_eq`: `σ • y` and `y` lie in the same orbit.
- `coeff_smul_of_invariant`: a `G`-fixed element has the same coordinate at `σ • y` as at `y`.
- `orbitSum_of_invariant`: for a `G`-fixed element `x`,
  `orbitSum (orbit of b) x = |orbit b| · x(b)`.
- `orbitSum_eq_zero_of_norm_eq_zero`: if `N x = 0`, then all orbit sums of `x` vanish.
- `single_sub_single_mem_range`: `δ_{g^n z} - δ_z ∈ range (ρ(g) - 1)`.
- `mem_range_of_orbitSum_eq_zero`: suppose `g` generates the finite group `G`. If all orbit
  sums of `x` vanish, then `x ∈ range (ρ(g) - 1)`.
- `subsingleton_subquotient_norm`: `ker N ⧸ range (ρ(g) - 1)` is trivial.
- `invariant_of_sub_one_eq_zero`: an element fixed by a generator is fixed by every element of
  the finite group.
- `natCard_subquotient_sub_one`: `|ker (ρ(g) - 1) ⧸ range N| = orbitStabilizerProduct G X`.
- The following assume `[Finite G] [IsCyclic G] [Finite X]`:
  - `subsingleton_groupCohomology_one_ofMulAction`: `H¹(G, ℤ[X])` is a subsingleton.
  - `natCard_groupCohomology_two_ofMulAction`:
    `Nat.card H²(G, ℤ[X]) = orbitStabilizerProduct G X`.
  - `hasHerbrandQuotient_ofMulAction`:
    `HasHerbrandQuotient (Rep.ofMulAction (ULift ℤ) G X) (orbitStabilizerProduct G X)`. So
    both groups are finite and `|H²| = (∏_O |G_O|) · |H¹|`.
