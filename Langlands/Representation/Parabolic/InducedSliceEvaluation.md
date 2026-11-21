# Faithful tensor evaluation from parabolic covariance

Let `e g : A → V` (for `g` in an index set `G`) be complex-linear inducing evaluations into a complex representation `ρ` of a monoid `L` on `V`. Let `j : I → Hom(V, S)` be a complex-linear family of maps out of the coefficient space. `pair j` sends `v ⊗ i` to `j(i)(v)`. `slices e j` sends a tensor in `A ⊗ I` to the function `g ↦ pair j ((e g ⊗ id) t)`, so a pure tensor `a ⊗ i` gives `g ↦ j(i)(e g a)`.

Spanning (`span_values_eq_top`). Assume `ρ` is irreducible and the evaluations satisfy the covariance `e(shift(p, g)) = χ(p) · ρ(p) ∘ e(g)` with every scalar `χ(p)` nonzero. Then the span of all values `e g a` is `ρ`-invariant: dividing by `χ(p)` writes `ρ(p)(e g a)` as a value. If some value `e g a` is nonzero, this invariant span is nonzero, and irreducibility makes it all of `V`.

Injectivity (`slices_injective`). Assume, in addition to irreducibility and the covariance with nonzero scalars, that:

- `j` is injective;
- the evaluations are jointly faithful: `a = 0` whenever `e g a = 0` for every `g`;
- every Levi self-intertwiner of `ρ` is a scalar multiple of the identity.

Suppose every slice of `t` vanishes. Fix `g` and let `y = (e g ⊗ id)(t)` in `V ⊗ I`. Testing at `shift(p, g)` and cancelling the nonzero scalar `χ(p)` gives `pair j ((ρ(p) ⊗ id)(y)) = 0` for every `p`, and hence for every element of the monoid algebra of `L`. If `y` were nonzero, some functional `φ` on `V` would give a nonzero contraction `i ∈ I`. Injectivity of `j` then gives a vector `v` with `j(i)(v) ≠ 0`. Because the commutant is scalar, Jacobson density gives a monoid algebra element acting like the rank-one map `φ(·) v` on the finitely many first-factor vectors of `y`. The vanishing tests then force `j(i)(v) = 0`, a contradiction. So `(e g ⊗ id)(t) = 0` for every `g`. Writing `t` in a basis of `I`, joint faithfulness of the evaluations makes each coordinate zero, so `t = 0`.

This is an internal algebraic lemma for the finite and infinite tensor product in Langlands, *On the notion of an automorphic representation* (1979), Lemma 1, printed p. 203, Corvallis Part I PDF p. 198.
