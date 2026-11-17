# Finite-order detection modulo an integer

Worker 330.

`Langlands.FiniteOrderCongruenceDetectionStatement.{u} : Prop` is a closed,
universe-polymorphic proposition definition. It states the algebraic input used
in the proof of Conrad's Corollary B.3.6, with the strengthened bound `3 ≤ n`.
A proof of this target is a separate task.

## Exact statement

For every type `M : Type u`, every additive commutative group structure on `M`,
every instance `AddGroup.FG M`, and every natural number `n` with `3 ≤ n`,
assume

```text
∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → n • x = 0.
```

Then for every actual additive automorphism `σ : M ≃+ M`, the assumptions

```text
∃ r : ℕ, 0 < r ∧ (σ.toEquiv : Equiv.Perm M) ^ r = 1
∀ x : M, ∃ y : M, σ x = x + n • y
```

imply `σ = AddEquiv.refl M`.

`AddGroup.FG M` is Mathlib's finite generation as an additive group: a finite
set generates the top additive subgroup. It places no torsion-free or freeness
condition on `M`. Both `k • x` and `n • x` are natural-number repeated addition.
The first premise therefore includes every element killed by some positive
integer, with no fixed annihilating integer assumed in the definition of
torsion.

The power in the finite-order premise is taken in the composition group of
permutations of `M`. The element `σ.toEquiv` is the underlying bijection of the
same additive automorphism. Thus a positive power equalling `1` says that a
positive number of compositions of `σ` is the identity; it is not a power of
the values in `M`. The conclusion is equality of additive equivalences and
hence implies `σ x = x` for all `x`.

## Quotient interpretation

Write `nM = {n • y | y ∈ M}`, an additive subgroup since `M` is abelian.
Every additive automorphism preserves this subgroup, because it commutes with
natural-number repeated addition and its inverse does too. It consequently
induces an automorphism of the actual quotient `M / nM`.

The pointwise congruence premise is precisely the condition that this induced
automorphism is the identity. Indeed, `σ x` and `x` have the same quotient
class exactly when `σ x - x ∈ nM`, equivalently when some `y : M` satisfies
`σ x = x + n • y`. This equivalence is an explanation of the chosen
formulation; this module does not add a separate quotient construction or
comparison theorem.

## Source and correspondence

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, Société Mathématique de France, 2014, proof of
Corollary B.3.6, pp.293–295, specifically the algebraic argument on p.294.
Registered source: `conrad-2014-reductive-group-schemes`; retained file
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`,
SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The cited three pages were read for this statement.

Conrad takes a finitely generated abelian group `M` and chooses `n > 3`
divisible by the exponent of its torsion subgroup. He shows that the kernel
of `Aut(M) → Aut(M/nM)` has no nonidentity finite-order element. The Lean
premises encode these conditions as follows:

| Source condition | Lean formulation |
| --- | --- |
| Finitely generated abelian group | `[AddCommGroup M] [AddGroup.FG M]` |
| Torsion subgroup killed by `n` | Every `x` killed by a positive `k` satisfies `n • x = 0` |
| Finite-order element of `Aut(M)` | A positive power of `σ.toEquiv` is the identity permutation |
| In the kernel of reduction modulo `nM` | `∀ x, ∃ y, σ x = x + n • y` |
| Trivial automorphism | `σ = AddEquiv.refl M` |

For finitely generated abelian groups the torsion subgroup is finite, so
annihilation by `n` is equivalent to the source's divisibility condition on
its exponent. No exponent, decomposition or choice of generators is added
as data to the target.

The bound `3 ≤ n` is a conventional strengthening of Conrad's sufficient
bound `3 < n`, rather than a literal translation of that bound. It includes
`n = 3`, using the usual torsion-freeness of the principal congruence kernel
in `GL_d(ℤ)` at level `3`. Conrad's remaining reduction also applies at that
level: pass to `M/M_tor`, then use that `nM` is torsion-free to eliminate the
torsion-valued difference from the identity. This records the provenance of
the strengthened statement; it supplies no Lean proof of that extra case or
of the general target.

## Scope

The universe `u` is arbitrary, and all groups, automorphisms and scalar
conditions refer to the same actual type `M`. There are no scheme, sheaf,
topology, Galois action or local-system hypotheses. The only imports are
Mathlib's additive-equivalence/permutation composition infrastructure and
finite group generation. No auxiliary definition or mathematical axiom is
introduced.
