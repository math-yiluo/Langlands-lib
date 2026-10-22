# Matching composition factors in length at most two

Worker 241 authored this statement pair. Provenance: derived from the proof of
Bernstein–Zelevinsky 1977, §2.16(1).

`Langlands.LengthTwoFactorMatchingCriterion.{uK,uG,uV,uW}` is a proposition
definition, with no proof of the proposition. It quantifies over a field
`k : Type uK`, a monoid `G : Type uG`, `k`-modules `V : Type uV` and
`W : Type uW`, and representations `ρ : Representation k G V` and
`σ : Representation k G W`. The four universes are independent. There is no
smoothness, finite-dimensionality, or finite-length premise.

## Hypotheses

1. Counts `μ : Subrepresentation ρ → ℕ` and `ν : Subrepresentation σ → ℕ` on
   the invariant subspaces. Both are strictly monotone: a strict inclusion of
   invariant subspaces strictly increases the count.
2. `μ ⊥ = 0` and `ν ⊥ = 0`: the zero subspace has count zero.
3. `μ ⊤ ≤ 2` and `ν ⊤ ≤ 2`: the whole space has count at most two.
4. Intertwining maps `A : ρ.IntertwiningMap σ` and
   `A' : σ.IntertwiningMap ρ`, both nonzero.
5. The counts add up along both maps:
   `μ ⊤ = μ A.ker + ν A.range` and `ν ⊤ = ν A'.ker + μ A'.range`.
   Here `ker` and `range` are Mathlib's kernel and range subrepresentations
   of an intertwining map.
6. If `S` is an invariant subspace of `ρ` with `μ S = 1`, and some `v ∈ S`
   has `A v ≠ 0`, then there is an equivalence of representations
   `ρ.Equiv σ`.
7. If `S'` is an invariant subspace of `σ` with `ν S' = 1`, and some
   `w ∈ S'` has `A' w ≠ 0`, then there is an equivalence `ρ.Equiv σ`.

## Conclusion

`HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ)`, from the imported
`Langlands.Representation.Filtration.ObjectDefinitions`. It asserts actual
finite zero-to-full filtrations of the same length `n` of both
representations whose successive quotients are irreducible, and a
permutation `e` of `Fin n` such that the `i`th quotient of the first is
equivalent to the `e i`th quotient of the second. Thus the composition factors
agree with multiplicities.

## Source and provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), §2.16(1), printed pages 449–450 / PDF pages 10–11, source ID
`bernstein-zelevinsky-1977-induced-i`, original PDF SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
retained original pages were read directly for this statement.

There, `π = i(ρ)` and `π' = i(ρ')` are induced from associated irreducible
cuspidal data with `l(M) = 2`, and `A : π → π'`, `A' : π' → π` are nonzero
morphisms. The count is the additive function `l'` of §2.14(2), the total
length of the Jacquet modules along the subgroups associated with `M`, with
`l'(π) = l'(π') = 2`. It is positive on nonzero subquotients by §2.14(1). The
authors show that either `π ≅ π'`, or `π` and `π'` have unique proper
submodules `π₀` and `π₀'` with `l' = 1`, killed by `A` and `A'`
respectively, and `π/π₀ ≅ π₀'`, `π'/π₀' ≅ π₀`. The step `A(π₀) = 0` uses
Frobenius reciprocity: outside the excluded case `π ≅ π'`, a count-one
submodule has no nonzero map to `π'`.

This statement isolates the lattice-theoretic part of that argument.
Restricting `l'` to invariant subspaces gives hypotheses 1–3 and 5:
positivity and additivity make it strictly monotone, and additivity along
`A` reads `l'(π) = l'(ker A) + l'(A(π))`. Hypotheses 6 and 7 record the
consequence of Frobenius reciprocity used in the source. The fully quantified
monoid-and-field formulation is a derived interface, not a verbatim assertion
of BZ77. It does not construct Jacquet modules or state the induced
representation theorem.
