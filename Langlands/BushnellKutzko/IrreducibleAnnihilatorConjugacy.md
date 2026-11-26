# Conjugacy of endomorphisms killed by one irreducible polynomial

The module `Langlands.BushnellKutzko.IrreducibleAnnihilatorConjugacy` proves one result of
linear algebra over a finite field.

```lean
theorem Langlands.BushnellKutzko.exists_linearEquiv_conj_of_aeval_irreducible
    {k W : Type*} [Field k] [Finite k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    {p : k[X]} (hp : Irreducible p) {A B : Module.End k W}
    (hA : aeval A p = 0) (hB : aeval B p = 0) :
    ∃ φ : W ≃ₗ[k] W, ∀ w, φ (A w) = B (φ w)
```

If two endomorphisms `A` and `B` of a finite-dimensional vector space `W` over a finite field
`k` are both killed by the same irreducible polynomial `p`, then `B = φ A φ⁻¹` for a
`k`-linear automorphism `φ` of `W`.

## Proof

Let `K = k[X]/(p)`, a field because `p` is irreducible
(`PrincipalIdealRing.isMaximal_of_irreducible`). Through Mathlib's `Module.AEval'`, the
endomorphism `A` makes `W` a `k[X]`-module in which `X` acts by `A`. Since `p(A) = 0`, this module
is torsion by the ideal `(p)`, hence a `K`-vector space (`Module.IsTorsionBySet.module`); the same
holds for `B`. The field `K` is finite over `k`, so finite. Both `K`-vector spaces have the
underlying set `W`, so `Module.natCard_eq_pow_finrank` gives
`|K|^{dim_K(W, A)} = |W| = |K|^{dim_K(W, B)}`, and the dimensions agree because `|K| > 1`.
`LinearEquiv.ofFinrankEq` gives a `K`-linear isomorphism between the two structures. It is
`k`-linear because `k` acts through `k[X]` and `K`, and it carries the action of `X`, which is `A`
on one side and `B` on the other.

The result is used in `Langlands.BushnellKutzko.LatticeChain.exists_layerEquiv_residue_intertwine`
for the successive quotients of a lattice chain, where `A` and `B` are multiplications by residues
with the same minimal polynomial; this is the semisimple normal form in Bushnell–Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993), (2.5.7)–(2.5.8), printed
pp. 79–80 (source `bushnell-kutzko-1993-admissible-dual-gln`).
