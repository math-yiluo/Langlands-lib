# Rational prime-adic polarization nondegeneracy from finite levels

This module proves
`Langlands.AbelianScheme.PrimeRationalPolarizationWeilNondegeneracyReductionStatement`
as the theorem
`Langlands.AbelianScheme.primeRationalPolarizationWeilNondegeneracyReduction`.
The statement is the implication

```text
GeometricFiniteWeilNondegeneracyStatement.{u} →
  AlgClosedPointDivisibilityStatement.{u} →
    PrimeRationalPolarizationWeilNondegeneracyStatement.{u}
```

It is conditional. Neither hypothesis is proved here, and the module does not
prove the prime-adic target by itself.

The classical argument is in Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`). Chapter XI, (11.23),
printed p.168, assembles the perfect finite pairings `e_{ℓ^m}` of (11.11) into a
perfect pairing on Tate modules. Chapter X, Corollary (10.7), printed p.144,
says that the rational Tate map of an isogeny is an isomorphism. The Lean proof
follows this outline, but works only with points over the geometric point
`Over.mk s`. It uses the helper modules
`Langlands.AbelianScheme.AlgClosedIsogenyPoints` and
`Langlands.AbelianScheme.Tate.PrimeAdicSeparation` described in their own
Markdown.

## Notation

The local notations name the existing Library constructions with all their
inputs. `levelPair` is `finiteWeilLevelBilinearMap`, the finite Weil pairing at
level `n`. `primePair` is `primeWeilBilinearMap`, the integral prime-adic
pairing between the Tate modules of `A` and of the dual group scheme `GD`.
Coordinate `n` of `primePair x z` is `levelPair (p ^ n) T x_n z_n`
(`evaluation_primeWeilValue`, which holds by `rfl`). `primeIntegralAlong lam` is
`primeWeilAlongHomBilinearMap`, which is `primePair x (map T p (groupHom lam) y)`
(`primeWeilAlongHomBilinearMap_apply`). `primeAlong lam` is
`primeRationalWeilAlongHomBilinearMap`. On pure tensors it equals
`(q * r) ⊗ primeIntegralAlong lam x y`
(`primeRationalWeilAlongHomBilinearMap_tmul`).

## Intermediate theorems

- `primeWeilBilinearMap_separatingLeft`. Assume that, at every level `p ^ n`, an
  `x` with `levelPair (p ^ n) T x y = 0` for all `y` is zero. Assume also that
  every coordinate projection of the Tate module of `GD` is surjective. Then
  `primePair` is left-separating. If `primePair x z = 0` for all `z`, fix `n`
  and a level point `w`. Write `w` as coordinate `n` of some `z`. Coordinate `n`
  of `primePair x z = 0` is `levelPair (p ^ n) T x_n w = 0`. So every
  coordinate `x_n` vanishes.
- `primeWeilBilinearMap_separatingRight`. The same argument on the other side,
  with surjective coordinate projections of the Tate module of `A`.
- `primeWeilAlongHomBilinearMap_nondegenerate`. Let `lam : A ⟶ DA`, where `DA`
  is the dual abelian scheme. Assume `primePair` separates on both sides. Let
  `N > 0` kill every point over `T` in the kernel of `groupHom lam`, and let `ψ`
  be a homomorphism of point groups with `ψ y ≫ groupHom lam = y ^ N`. Then
  `primeIntegralAlong lam` is nondegenerate.
  - Left: suppose `primeIntegralAlong lam x y = 0` for all `y`. For any `z` in
    the dual Tate module, `exists_map_eq_natCast_smul` gives `y` with
    `map lam y = N • z`. Then `N • primePair x z = primePair x (map lam y) = 0`.
    The twist has no `p`-torsion (`TateTwist.eq_zero_of_prime_smul_eq_zero`),
    so `primePair x z = 0`. Left separation of `primePair` gives `x = 0`.
  - Right: suppose `primeIntegralAlong lam x y = 0` for all `x`. Right
    separation of `primePair` gives `map lam y = 0`. Then
    `eq_zero_of_map_eq_zero` gives `y = 0`.
- `primeRationalWeilAlongHomBilinearMap_nondegenerate`. If
  `primeIntegralAlong lam` is nondegenerate, so is `primeAlong lam`. Apply
  `separatingLeft_of_tmul` and `separatingRight_of_tmul` with the pure-tensor
  formula and torsion-freeness of the twist.

## The main proof

Introduce the two hypotheses `finiteLevel` and `divisibility`, then all
quantified data of the target. These are the ten propositions, the base `S`, the
abelian scheme `A` with its dual inputs, the polarization `lam` with
`hlam : IsPolarization ... lam`, the algebraically closed field `K`, the point
`s`, the prime `p` and `hp : (p : K) ≠ 0`.

1. Since `(p : K) ≠ 0`, also `((p ^ n : ℕ) : K) ≠ 0` for every `n`. So
   `finiteLevel` applied with `p ^ n` gives trivial left and right kernels of
   `levelPair (p ^ n) (Over.mk s)` for all `n`.
2. `hlam.1` says that `groupHom lam` is an isogeny.
   `IsIsogeny.exists_points_quasiInverse` at `s` gives `N > 0`, the kernel bound
   and `ψ`.
3. `divisibility` with `m = p`, applied to the dual abelian scheme
   `dualAbelianSchemeFromEvaluation ...` and to `A`, says that every point over
   `s` has a `p`-th root. By `evaluation_surjective_of_pow`, all coordinate
   projections of both Tate modules at `Over.mk s` are surjective.
4. Steps 1 and 3 give left and right separation of `primePair` at `Over.mk s`.
   Step 2 and `primeWeilAlongHomBilinearMap_nondegenerate` give nondegeneracy
   of the integral pullback pairing. Its rationalization `primeAlong lam` is
   then nondegenerate, which is the target.

Only the first conjunct of `hlam`, the isogeny property, is used. Symmetry and
ampleness of the polarization are not needed for nondegeneracy. The divisibility
hypothesis is applied to two different abelian schemes. This is why the
statement quantifies it globally.

The proof adds no hypotheses beyond those of the statement. It uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
