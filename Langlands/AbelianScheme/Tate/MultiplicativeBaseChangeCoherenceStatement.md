# Coherence statements for multiplicative Tate base change

This file states ten identity and composition laws for the existing canonical
base-change comparisons of the multiplicative group scheme. Its declarations
are proposition-valued definitions; this file supplies no proofs of these laws.
The entry declaration is
`Langlands.GroupScheme.Gm.TateComparison.MultiplicativeBaseChangeCoherence`,
the conjunction of all ten laws in the order described below.

## Objects and canonical identifications

All schemes and test schemes lie in one arbitrary universe. For a morphism
`b : S' ⟶ S` and `T : Over S'`, the functor `Over.map b` retains the underlying
scheme of `T` and composes its structure morphism with `b`. The five existing
comparisons send the actual multiplicative Tate object over `S'` at `T` to the
corresponding object over `S` at `(Over.map b).obj T`:

| Object | Parameters | Comparison | Test restriction |
| --- | --- | --- | --- |
| Actual torsion sections `Tate.Level` | Any `n : ℕ`, including zero | `levelBaseChange` | `Tate.levelRestrict` |
| Selected integral inverse limit `Tate.Integral` | Any `P : ℕ → Prop`, selecting positive orders | `integralBaseChange` | `Tate.testRestrict` |
| Integral prime-adic module `Tate.PrimeAdic.Integral` | `p : ℕ` with `Fact p.Prime` | `primeIntegralBaseChange` | `Tate.PrimeAdic.testRestrict` |
| Selected rational module `Tate.Rational` | Any `P : ℕ → Prop`; tensor with `ℚ` over `ℤ` | `rationalBaseChange` | `Tate.rationalTestRestrict` |
| Rational prime-adic module `Tate.PrimeAdic.Rational` | Prime `p`; tensor with `ℚ_[p]` over `ℤ_[p]` | `primeRationalBaseChange` | `Tate.PrimeAdic.rationalTestRestrict` |

The comparison names in the table belong to
`Langlands.GroupScheme.Gm.TateComparison`; the restriction names belong to
`Langlands.GroupScheme`. The group object in every Tate expression is
`(Gm S).toGrp` at its indicated base. The finite comparison is linear over
`ZMod n`, the selected integral comparison is continuous and linear over the
profinite integers, and the prime integral comparison is continuous and linear
over `ℤ_[p]`. The rational comparisons are algebraic linear equivalences over
`ℚ` and `ℚ_[p]`, respectively.

The target test schemes are canonically isomorphic, rather than silently
identified. For identity base change use

```lean
(Over.mapId S).hom.app T : (Over.map (𝟙 S)).obj T ⟶ T
```

and for `c : S'' ⟶ S'` followed by `b : S' ⟶ S` use

```lean
(Over.mapComp c b).hom.app T :
  (Over.map (c ≫ b)).obj T ⟶ (Over.map b).obj ((Over.map c).obj T)
```

Their underlying scheme morphisms are identities. Test restriction is
contravariant, so these arrows send sections at the unaltered or iterated test
scheme to the target used by the single base-change comparison.

## The ten laws

For any one row of the table, write `B_b,T` for its comparison and `R_a` for its
test restriction, keeping the row's order, predicate or prime parameter fixed.
The identity law quantifies every scheme `S`, every `T : Over S`, all parameters
in that row, and every element `x` of the row's actual Tate object at `T`. It is

```text
B_id,T(x) = R_((Over.mapId S).hom.app T)(x).
```

The composition law quantifies arbitrary schemes `S`, `S'`, `S''`, morphisms
`b : S' ⟶ S` and `c : S'' ⟶ S'`, every `T : Over S''`, all row parameters, and
every element `x` of the row's actual Tate object over `S''` at `T`. It is

```text
B_(c≫b),T(x) =
  R_((Over.mapComp c b).hom.app T)(B_b,(Over.map c).obj T(B_c,T(x))).
```

These formulas describe elementwise equalities in a common target. No arbitrary
base-change equivalence or coherence witness is a hypothesis. The ten exact
proposition names, grouped by the table's rows, are:

1. `LevelBaseChangeIdentity` and `LevelBaseChangeComposition`.
2. `IntegralBaseChangeIdentity` and `IntegralBaseChangeComposition`.
3. `PrimeIntegralBaseChangeIdentity` and `PrimeIntegralBaseChangeComposition`.
4. `RationalBaseChangeIdentity` and `RationalBaseChangeComposition`.
5. `PrimeRationalBaseChangeIdentity` and `PrimeRationalBaseChangeComposition`.

`MultiplicativeBaseChangeCoherence` conjoins the identity and composition law
for each row, in that order. The selected integral and rational laws include
the full choice `P(n) = True` and the away choice `P(n) = Nat.Coprime n m` for
any natural modulus `m`. This specializes the same underlying selected maps;
there is no additional claim about finite-adelic bundled maps in this target.

## Provenance and scope

These are internal coherence targets for the concrete constructions in
`MultiplicativeIntegralBaseChange`, `MultiplicativePrimeBaseChange`,
`MultiplicativeRationalBaseChange`, and
`MultiplicativeRationalPrimeBaseChange`. The finite construction is identified
there with actual torsion pullback after the inverse canonical Gm base-change
isomorphism. The integral constructions have this map at each coordinate; the
rational constructions extend those integral maps along their respective scalar
rings. The test restrictions are the existing restrictions of actual torsion
sections and their inverse-limit or tensor extensions. Mathlib's `Over.mapId`
and `Over.mapComp` supply the displayed canonical identifications. This explains
the provenance and direction of the proposed laws, without treating them as
already proved or attributing them to an external literature theorem.

There is no assumption of finite étaleness, characteristic zero, invertibility
of the torsion order, or finite rank: only the actual section objects and their
canonical comparisons occur. No roots, basis, or Tate-twist trivialization are
chosen. This statement unit does not assert monodromy pullback, pairing
compatibility, a rational topology, a restricted-product comparison, or
completion of the PEL level-structure task. A proof of the exact published
conjunction is a separate contribution.
