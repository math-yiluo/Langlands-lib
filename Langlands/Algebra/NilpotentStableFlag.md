# Stable flags for nilpotent families of endomorphisms

Author: Worker 1429 (statement proposed by Worker 1498).

## Statement

`Langlands.Algebra.exists_stable_flag_of_isNilpotent` works over an arbitrary
field `k` and a finite-dimensional `k`-vector space `V`. On `Module.End k V`,
the bracket is the ring commutator `⁅f, g⁆ = f * g - g * f`, which the module
enables through the local instance `LieRing.ofAssociativeRing`. The hypotheses
are:

- `A` is a `k`-subspace of `Module.End k V` closed under the commutator
  (`hlie`), and every element of `A` is nilpotent (`hnil`);
- `S` is a set of endomorphisms with `⁅g, a⁆ ∈ A` for every `g ∈ S` and
  `a ∈ A` (`hS`).

The conclusion gives a sequence `F : ℕ → Submodule k V` and an index `m` such
that:

- `F` is antitone;
- `F 0 = ⊤` and `F m = ⊥`;
- `a (F t) ⊆ F (t + 1)` for every `a ∈ A` and every `t`;
- `g (F t) ⊆ F t` for every `g ∈ S` and every `t`.

### Provenance

This is an internal helper for the proof of
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement`; Worker 1498
proposed the exact statement. It applies Engel's theorem for a Lie algebra of
nilpotent endomorphisms (cf. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §3.3). Stability of the flag under the normalizing set
`S` is a direct computation, carried out below.

## Proof

Regard `A` as a Lie subalgebra `L` of `Module.End k V`; its action on `V` is the
given one, so `toEnd k L V x = x`. Every element of `L` is nilpotent. Engel's
theorem for Noetherian modules, `LieModule.isNilpotent_iff_forall'`, therefore
makes `V` a nilpotent `L`-module. Some term `m` of the lower central series of
`V` is then `⊥` (`LieModule.isNilpotent_iff`).

Take `F t` to be the underlying subspace of `lowerCentralSeries k L V t`. The
series is antitone (`antitone_lowerCentralSeries`) and starts at `⊤`. Since
`F (t + 1) = ⁅⊤, F t⁆`, each `a ∈ A` maps `F t` into `F (t + 1)`.

Stability under `g ∈ S` is proved by induction on `t`; the case `t = 0` is
trivial. By `LieSubmodule.lieIdeal_oper_eq_linear_span`, `F (t + 1)` is
spanned by the vectors `a n` with `a ∈ A` and `n ∈ F t`. It therefore suffices
that `g (a n)` lies in `F (t + 1)`. The identity
`g (a n) = a (g n) + ⁅g, a⁆ n` shows this: `g n ∈ F t` by the induction
hypothesis, and `⁅g, a⁆ ∈ A` by `hS`.
