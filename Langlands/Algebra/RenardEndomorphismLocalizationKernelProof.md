# Kernel and inverse-power exhaustion of the actual endomorphism localization: proof

Author: Worker 900, for proof task `27b06f5a-9788-4307-b9d1-950763a472ec`
under the whole-book Renard parent `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
The target statement was published in Library commit
`cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b`.

## Target

The module `Langlands.Algebra.RenardEndomorphismLocalizationKernelProof`
imports the published statement module
`Langlands.Algebra.RenardEndomorphismLocalizationStatements` unchanged and
proves

```lean
theorem kernelExhaustionStatements : KernelExhaustionStatements.{u, v}
```

in namespace `Langlands.Renard.EndomorphismLocalization`. The theorem has no
section parameters; its type is exactly the published aggregate: the ring
statement `KernelExhaustionStatement.{u,v}` together with the field
specialization `FieldKernelExhaustionStatement.{u,v}`. The coefficient
universe `u` and the module universe `v` are independent.

## Helper theorems

Every helper is stated for an arbitrary commutative unital ring `R : Type u`,
an `R`-module `V : Type v` and an arbitrary endomorphism `a : Module.End R V`.
None assumes finite generation, finite dimension, Noetherianity,
nontriviality or injectivity, except the displayed hypothesis of
`iota_injective`. The helpers use only the published construction
`Langlands.Algebra.RenardEndomorphismLocalization` (`Localized`, `iota`,
`localizedInv`, `frac`) and do not redefine it.

- `iota_eq_zero_iff a z : iota a z = 0 ↔ ∃ n, (a ^ n) z = 0`.
  The proof writes `iota a z` as `frac a z 0` (`frac_zero`) and `0` as
  `frac a 0 0` (from `frac_zero` and `map_zero`). The published equality
  criterion `frac_eq_frac_iff` then says the two fractions are equal exactly
  when `(a ^ (k + 0)) z = (a ^ (k + 0)) 0` for some `k`. `simp` with
  `add_zero` and `map_zero` reduces this to `∃ k, (a ^ k) z = 0`.
- `ker_pow_monotone a : Monotone (fun n => LinearMap.ker (a ^ n))`.
  If `m ≤ n`, write `n = k + m`. Then `a ^ n = a ^ k * a ^ m`
  (`pow_add` after `add_comm`), so `(a ^ m) x = 0` gives `(a ^ n) x = 0`.
- `ker_iota_eq_iSup a : LinearMap.ker (iota a) = ⨆ n, LinearMap.ker (a ^ n)`.
  The proof works elementwise. Because the power kernels are monotone, the
  family is directed, so `Submodule.mem_iSup_of_directed` turns membership in
  the supremum into membership in some single `LinearMap.ker (a ^ n)`. That
  is the right side of `iota_eq_zero_iff`.
- `iota_injective a (ha : Function.Injective a) :
  Function.Injective (iota a)`.
  By `LinearMap.ker_eq_bot'` it is enough to show that `iota a z = 0`
  forces `z = 0`. The criterion gives some `n` with `(a ^ n) z = 0`.
  The map `a ^ n` is the `n`-th iterate of `a` (`Module.End.coe_pow`), so it
  is injective (`Function.Injective.iterate`), and `(a ^ n) z = (a ^ n) 0`
  gives `z = 0`.
- `iUnion_range_localizedInv_pow a :
  (⋃ n, Set.range ((localizedInv a ^ n).comp (iota a))) = Set.univ`.
  This is a literal equality of sets in `Localized a`. For any element
  `z`, the published lemma `frac_surjective` gives `w` and `n` with
  `frac a w n = z`. Then `frac_eq_localizedInv_pow` rewrites this as
  `(localizedInv a ^ n) (iota a w)`. So `z` lies in the `n`-th member of the
  union, witnessed by `w`.

## Aggregate

`kernelExhaustionStatements` is the anonymous-constructor pair of:

1. the ring statement: each of the four closed propositions
   `KernelCriterionStatement`, `KernelUnionStatement`,
   `InjectivityStatement` and `PowerExhaustionStatement` is proved by
   introducing the ring, module, instances and endomorphism, then applying
   the matching helper;
2. the field statement: for any field `k`, `k`-module `V` and endomorphism
   `a`, the four conjuncts come from the same helpers. A field is a
   commutative ring, so the helpers apply through instance inference.

## Relation to the source

The book's route is not needed for this proof. The field implication matches
Renard 2026, A.III.1, lemma (i) after example 5 (printed253/PDF259). The
kernel equalities and the literal exhaustion are the derived formulations
recorded in the paired statement Markdown. The extension to commutative
rings is internal. This module proves nothing beyond the published
aggregate. The quotient, comparison, converse, B-action and C.II obligations
of parent `f5d1f399-a1f8-4ab5-a981-90b92abd4857` remain open.
