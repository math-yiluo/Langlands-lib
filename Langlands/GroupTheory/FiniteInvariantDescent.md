# Descending an invariant by a finite cardinality bound

This internal algebraic construction isolates the finite-cardinality argument in Artin–Tate, *Class Field Theory* (2009), Chapter VII §3, Lemma 6, printed p.49 (PDF p.58). It is a conditional auxiliary construction and does not prove a global invariant theorem.

For additive groups `A`, `B`, and `D` in independent universes, let `j : A →+ B` and `s : A →+ D`. Assume `ker j ≤ ker s`. The map `onRange` is the unique descent of `s` to the subgroup `j.range`, implemented with Mathlib's `AddMonoidHom.liftOfSurjective` applied to the range restriction of `j`. Its value on `j.rangeRestrict a` is `s a`. Surjectivity of `s` therefore implies surjectivity of `onRange`.

Now suppose `B` is finite, `s` is surjective, and `Nat.card B ≤ Nat.card D`. Surjectivity gives `Nat.card D ≤ Nat.card j.range`, while subgroup inclusion gives `Nat.card j.range ≤ Nat.card B`. Thus the image of `j` is all of `B`, and `onRange` is bijective. The definition `equiv` composes the inverse of the subgroup inclusion with this bijective descent to give `B ≃+ D`. The theorem `equiv_apply` proves `equiv (j a) = s a`; `equiv_unique` proves uniqueness among additive homomorphisms satisfying that identity. Finally, injectivity of this equivalence upgrades the initial kernel inclusion to `ker j = ker s`.

No finiteness of `A` is assumed. Finiteness of `D` follows from the surjection from the finite subgroup `j.range`; an infinite source is allowed. The construction applies to additive groups, without requiring commutativity.

In the intended cyclic global application, `A` will be actual idele cohomology, `B` actual idele-class cohomology, and `D` the degree-denominator subgroup of `ℚ/ℤ`. Exactness and reciprocity must still establish the kernel inclusion; local classes and the arithmetic existence of primes must establish surjectivity onto `D`; the inequalities and H¹ vanishing must establish the cardinality bound and finiteness of `B`. This file supplies none of those arithmetic hypotheses. In particular, it does not assert surjectivity of the idele-to-idele-class cohomology map for general noncyclic extensions.

The proof is derived from the finite cardinality comparison and Mathlib's existing descent API. Artin–Tate motivates this abstraction through a class of invariant `1/n` and an order bound; the Lean interface instead accepts a surjective map into a target of the required cardinality. The original source does not state this general additive-group formulation.

The complete unapplied declaration has the following parameter shape:

```lean
Langlands.FiniteInvariantDescent.equiv.{u, v, w}
  {A : Type u} {B : Type v} {D : Type w}
  [AddGroup A] [AddGroup B] [AddGroup D]
  (j : A →+ B) (s : A →+ D) (hker : j.ker ≤ s.ker)
  [Finite B] (hs : Function.Surjective s)
  (hcard : Nat.card B ≤ Nat.card D) : B ≃+ D
```

Development inspection checked the unapplied definition at universes `u`, `v`, and `w`, with only `propext`, `Classical.choice`, and `Quot.sound`. The complete module built without errors or warnings. This is a construction check, not acceptance of any global arithmetic theorem.
