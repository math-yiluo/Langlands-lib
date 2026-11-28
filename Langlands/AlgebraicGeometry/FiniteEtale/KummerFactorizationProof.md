# Proof of Kummer factorization over a strictly Henselian regular local ring

The module `Langlands.AlgebraicGeometry.FiniteEtale.KummerFactorizationProof`
proves `StrictlyHenselianKummerFactorizationStatement` from the module
`KummerFactorizationStatement`:

`strictlyHenselianKummerFactorization :
StrictlyHenselianKummerFactorizationStatement.{u, v}`.

So for a strictly Henselian regular local domain `R`, a regular parameter `t`,
a prime `ℓ` invertible in `R`, a geometric point `x` of `U = Spec R[1/t]` and a
continuous homomorphism `ρ` from `π₁(U, x)` to a finite discrete `ℓ`-group
`H`, there are `n` and a geometric point `y` of the Kummer cover
`U_n = Spec R[1/t][X]/(X^(ℓ^n) - t)` over `x` such that `ρ` is trivial on the
image of `π₁(U_n, y)`. The proof takes `n = k + 1`, where `|H| = ℓ^k`.
Declarations are in the namespace `Langlands.AlgebraicGeometry.FiniteEtale`.

## Group theory

For a group `G`:

- `exists_surjective_ker_eq_of_index_eq`: a subgroup `Q` of index `ℓ` of a
  finite `ℓ`-group `P` is the kernel of a surjective homomorphism onto any
  group `M` of order `ℓ`. (A maximal subgroup of a nilpotent group is normal,
  Mathlib's `NormalizerCondition.normal_of_coatom`, and `P/Q ≃ M` as both
  have prime order `ℓ`.)
- `exists_index_eq_prime`: a nontrivial finite `ℓ`-group has a subgroup of
  index `ℓ` (a maximal subgroup, by coatomicity and
  `IsPGroup.isCoatom_iff_index_eq_prime`).
- `isCyclic_of_forall_ker_comp_eq`: let `f : G →* P` be surjective onto a
  finite `ℓ`-group and `M` of order `ℓ`. If `ker (χ ∘ f)` is one and the same
  subgroup `K` of `G` for every surjective `χ : P → M`, then `P` is cyclic.
  Otherwise Mathlib's `IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime`
  gives two distinct subgroups `Q₁ ≠ Q₂` of index `ℓ`. Both pull back to `K`,
  and `f` is surjective, so `Q₁ = f(K) = Q₂`.
- `ker_eq_ker_of_le`: if `χ, κ : G → M`, `|M| = ℓ` prime, `χ` is surjective,
  `κ ≠ 1` and `ker χ ≤ ker κ`, then `ker χ = ker κ`. Both kernels have index
  `ℓ` (`Subgroup.index_ker`), and `Subgroup.relIndex_mul_index` forces the
  relative index to be `1`.
- `ker_le_ker_of_isCyclic_range`: if `κ : G → M` is surjective onto a finite
  group, `h^|M| = 1` for all `h ∈ H`, and the image of
  `ρ.prod κ : G → H × M` is cyclic, then `ker κ ≤ ker ρ`. The image has
  exponent dividing `|M|`; being cyclic, its order is its exponent, hence at
  most `|M|`. Its projection to `M` is surjective, hence bijective, so
  `κ(g) = 1` forces `(ρ(g), κ(g)) = 1`.

## Surjectivity of the Kummer characters

- `isUnit_natCast_prime_pow`: if `ℓ` is invertible in `R`, so is `ℓ^k`.
- `parameterKummerCharacter_surjective`: if the Kummer character of level `ℓ`
  of `t` (`parameterKummerCharacter`, module `KummerCyclicQuotient`) is
  nontrivial, then the Kummer character `κ_N` of level `N = ℓ^(k+1)` is
  surjective onto `rootsOfUnity N R`. Pick `g₀` with `κ_ℓ(g₀) ≠ 1`. By
  `kummerCharacter_level`, `κ_ℓ(g₀) = κ_N(g₀)^(ℓ^k)` in `R`, so
  `κ_N(g₀)^(ℓ^k) ≠ 1` and `κ_N(g₀)^(ℓ^(k+1)) = 1`. Hence `κ_N(g₀)` has order
  `ℓ^(k+1)` (`orderOf_eq_prime_pow`) and generates the group, which has
  `ℓ^(k+1)` elements (`card_rootsOfUnity_eq`).

## Kummer characters control `ρ`

`ker_parameterKummerCharacter_le_ker` assumes the hypotheses of the statement
on `R`, `t`, `ℓ` and `x`, a finite discrete group `H` with
`Nat.card H = ℓ^k`, and a continuous `ρ : π₁(U, x) →* H`. It concludes
`ker κ_N ≤ ker ρ` for `N = ℓ^(k+1)`.

1. If `ρ = 1` there is nothing to prove. Otherwise let `P` be the image of
   `ρ.prod κ_N : π₁(U, x) → H × μ_N(R)`, a subgroup of a group of order
   `ℓ^k · ℓ^(k+1)`, hence an `ℓ`-group, and nontrivial since `ρ ≠ 1`.
   Its kernel `ker ρ ⊓ ker κ_N` is open: `ρ` is continuous with discrete
   target and `ker κ_N` is open (`isOpen_ker_kummerCharacter`).
2. For every surjective `χ : P → μ_ℓ(R)`, the composite `χ'` of `χ` with
   `π₁(U, x) → P` is surjective with open kernel (it contains the open kernel
   of step 1). By `ker_le_ker_parameterKummerCharacter` (module
   `KummerCyclicQuotient`), `ker χ' ≤ ker κ_ℓ` and `κ_ℓ ≠ 1`; by
   `ker_eq_ker_of_le`, `ker χ' = ker κ_ℓ`.
3. By `isCyclic_of_forall_ker_comp_eq` with `K = ker κ_ℓ`, `P` is cyclic.
4. Since `P` is a nontrivial `ℓ`-group, it has a subgroup of index `ℓ` and a
   surjection onto `μ_ℓ(R)` (`exists_index_eq_prime`,
   `exists_surjective_ker_eq_of_index_eq`). Step 2 for it gives `κ_ℓ ≠ 1`, so
   `κ_N` is surjective by `parameterKummerCharacter_surjective`.
5. Every `h ∈ H` satisfies `h^N = (h^(ℓ^k))^ℓ = 1`, and `|μ_N(R)| = N`. So
   `ker_le_ker_of_isCyclic_range` gives `ker κ_N ≤ ker ρ`.

## The main theorem

`strictlyHenselianKummerFactorization`: given the data of the statement,
write `|H| = ℓ^k` (`IsPGroup.iff_card`) and put `n = k + 1`. The Kummer fibre
over `x` is nonempty (`kummerFiber_nonempty`, module `KummerCovers`, as `Ω`
is algebraically closed); choose a point `p` and let `y = p.left`, so
`y ≫ kummerMorphism t (ℓ^n) = x` (`Over.w p`). For `g ∈ π₁(U_n, y)`, its
image in `π₁(U, x)` fixes the point `p` of the fibre of the Kummer cover (the
Library's `fundamentalGroupMap_fixes_lift`, module `CoverPointStabilizer`).
The kernel of `κ_N` is the stabilizer of `p` (`ker_kummerCharacter`), so the
image lies in `ker κ_N ≤ ker ρ`, and `ρ` composed with `fundamentalGroupMap`
is trivial.

## Provenance

The statement follows SGA 7 I, Exposé I, 0.3–0.4 (P. Deligne, *Résumé des
premiers exposés de A. Grothendieck*), registered as
`deligne-1972-sga7-i-expose-i-monodromie`, and the Stacks Project, *Fundamental
Groups of Schemes*, Lemma 58.31.5 (Tag 0EYG), registered as
`stacks-tame-ramification-58-31-0BSE-2026-11-27`; see the page of
`KummerFactorizationStatement`. Deligne describes the tame quotient `I/P`
as an inverse limit of groups of roots of unity. In the `ℓ`-primary case,
the image of `P` is trivial since a nontrivial finite `ℓ`-group has a
quotient of order `ℓ` and `ℓ` is invertible on the divisor.

The Lean proof classifies order-`ℓ` quotients directly by Kummer theory
over `R[1/t]` with `Pic R[1/t] = 0` (module `KummerCyclicQuotient`). It
then uses the fact that a finite `ℓ`-group whose index-`ℓ` subgroups all
coincide is cyclic.
