# Faces of a chamber and admissible types

Fix `hΨ : IsAffineRootSystemWithRankZero Ψ` on a real affine space `A` over `V`
(independent universes `uV`, `uA`), a regular point `c`, its chamber
`C = facet Ψ c`, and `S = chamberSimpleReflections Ψ C`. The main theorem,
`exists_mem_facetClosure_fixingSimpleReflections_eq`, proves the following. For
every admissible type `X` (`IsAdmissibleType S X`, KP Definition 1.5.17(1)),
some point `x` of the closure of `C` satisfies
`fixingSimpleReflections Ψ C x = X`. Together with the existing
`isAdmissibleType_facetSimpleReflections`, this shows that the type map
`Fa ↦ facetSimpleReflections Ψ C Fa` is a bijection from the faces of `C` onto
the admissible types. It also reverses the face order.

Source correspondence: in the proof of KP Proposition 7.5.6(2) (book
pp. 262–263), the facets of `C` correspond to the admissible types. In the
irreducible case KP associates to a proper subset of the simple reflections the
face of the simplex `C` spanned by the complementary vertices (KP Remark 1.3.16
and Proposition 1.3.22(6), citing Bourbaki). The general case is reduced to it
by a product decomposition. This module does not use the irreducible
decomposition or the simplex structure. It is an internal deduction from the
existing affine-root APIs and the frozen units `AffineChamberSimpleCone`,
`AffineSimpleFixedAdmissible` and `AffineSimpleRootGram`, through the
linear-algebra argument below. It introduces no external assertion.

## Isotropic combinations

The first section is pure linear algebra over a finite index type `ι`, with
functionals `f : ι → V*` and a finite set `T ⊆ V`.
`IsIsotropicCombination f T n` means `Σ_i n_i f_i(v) = 0` for every `v ∈ T`. It
is closed under differences and scalar multiples (`.sub`, `.smul`). The
abbreviation `combinationGram f T i j` is the Gram matrix
`G(i,j) = Σ_{v∈T} f_i(v) f_j(v)`.

* `sum_sq_combination_eq` expands `Σ_v (Σ_i m_i f_i(v))²` as
  `Σ_{i,j} m_i m_j G(i,j)`.
* `IsIsotropicCombination.abs`: if `G(i,j) ≤ 0` for `i ≠ j`, then `|n|` is
  isotropic whenever `n` is. Termwise `|n_i||n_j| G(i,j) ≤ n_i n_j G(i,j)`, so
  the sum of squares for `|n|` is at most that for `n`, which is `0`. Hence
  every square vanishes.
* `IsIsotropicCombination.sum_mul_gram`: `Σ_k n_k G(i,k) = 0` for isotropic `n`.
* `IsIsotropicCombination.eq_zero_of_gram_ne_zero` (the Perron–Frobenius step):
  under the same sign hypothesis, if `n` is isotropic, `n_i = 0` and
  `G(i,j) ≠ 0`, then `n_j = 0`. Row `i` of `G|n|` is a sum of nonpositive terms
  `|n_k| G(i,k)` (the term `k = i` vanishes) equal to `0`. So each term
  vanishes, in particular `|n_j| G(i,j)`.

`exists_forall_apply_eq_of_relations` is the duality step. Let `b : ι → ℝ`
satisfy `Σ_i n_i b_i = 0` for every relation `n` with `Σ_i n_i f_i = 0`. Then
some `d ∈ V` has `f_i(d) = b_i` for all `i`. Otherwise `b` is outside the range
of `LinearMap.pi f`. Mathlib's `Submodule.exists_dual_map_eq_bot_of_notMem`
gives a functional `φ` killing that range with `φ(b) ≠ 0`.
`LinearMap.pi_apply_eq_sum_univ` writes `φ` as `y ↦ Σ_i n_i y_i`. This `n` is a
relation, so `φ(b) = 0`, a contradiction.

## Points of the closed chamber with prescribed type

`exists_eq_smul_chamberSimpleRoot`: every simple root `φ` of `C` is `r` times
the chosen root `chamberSimpleRoot s` of a simple reflection `s`, with
`r > 0`. Take `s` to be the reflection of `φ`. The existing
`exists_eq_smul_of_affineReflection_eq` gives proportionality, and both roots
are positive at `c`.

`exists_mem_facetClosure_fixingSimpleReflections_eq`: index by the finite set
`S` (`finite_chamberSimpleReflections`). Take `f_s = ψ̇_s`, the derivatives of
the chosen roots, and `T` the finite coroot set. By `chamberSimpleGram_nonpos`
the off-diagonal Gram entries are `≤ 0`. By `chamberSimpleGram_ne_zero` they
are nonzero for noncommuting reflections. Hence, for isotropic `n`:

* zero propagation: `n_s = 0` and `SameComponent S s t` give `n_t = 0`, by
  induction along the noncommutation chain;
* positivity: `n_s > 0` gives `n_t > 0` on the component of `s`. Apply
  propagation to `|n| - n`, and to `n` with `sameComponent_symm`;
* proportionality: if `p` is isotropic with `p_t ≠ 0`, then
  `n_s = (n_t / p_t) p_s` on the component of `t`. Apply propagation to
  `n - (n_t/p_t) p`.

For each `t`, `P t` is `|p|` for a chosen isotropic `p` with `p_t ≠ 0` if one
exists, and `0` otherwise. `F t` is the finite set of `s` in the component of
`t` outside `X`. It is nonempty because `X` is admissible. Put `ψc s = ψ_s(c) > 0`
and, for `t ∈ X`,

```
w t s = -ψc t                                if s = t,
w t s = ψc t · P t t / (P t s · #(F t))      if s ∈ F t,
w t s = 0                                    otherwise,
```

and `b s = ψc s + Σ_{t ∈ X} w t s`. Then `b s = 0` for `s ∈ X`, since only
`t = s` contributes. Also `b s > 0` for `s ∉ X`, since all contributions are
nonnegative.

Every relation `n` (`Σ_s n_s ψ̇_s = 0`) is isotropic. For each `t ∈ X`,
`Σ_s n_s w t s = -n_t ψc t + Σ_{s∈F t} n_s ψc t P t t /(P t s #(F t))`. If
`P t t > 0`, proportionality turns each summand into `n_t ψc t / #(F t)`, so the
total is `0`. Otherwise no isotropic vector is nonzero at `t`, so `n_t = 0` and
`P t = 0`, and every term vanishes. Hence `Σ_s n_s (b_s - ψc s) = 0`, and the
duality step gives `d` with `ψ̇_s(d) = b_s - ψc s`. The point `x = d +ᵥ c`
satisfies `ψ_s(x) = b_s`. Every simple root is a positive multiple of some
`ψ_s`, so it is nonnegative at `x`, and `x` is in the closure
(`mem_facetClosure_iff_simple_nonneg`). Finally `s` fixes `x` exactly when
`b_s = 0`, that is, exactly when `s ∈ X`.

## Faces and the order

`apply_eq_zero_of_simple_zero_imp`: for `x, y` in the closure, if every simple
root vanishing at `x` vanishes at `y`, then every root vanishing at `x`
vanishes at `y`. This is the one-sided form of the argument in
`AffineChamberSimpleCone` (a segment point beyond `x` would leave the closure).
`simple_zero_imp_of_fixingSimpleReflections_subset` translates inclusion of
fixing sets into this hypothesis.

`mem_facetClosure_iff_fixingSimpleReflections_subset`: for `x, y` in the
closure, `x ∈ facetClosure Ψ y` exactly when every simple reflection fixing `y`
fixes `x`. `facetRel_of_fixingSimpleReflections_eq`: equal fixing sets give the
same facet.

`exists_eq_facet_of_isFaceOf` and `isFaceOf_facet_of_mem_facetClosure`
identify the faces of `C` (existing `IsFaceOf`) with the facets of points of
its closure. `exists_isFaceOf_facetSimpleReflections_eq` restates the main
theorem for faces, using `facetSimpleReflections_facet_eq`.

`bijOn_facetSimpleReflections`: `facetSimpleReflections Ψ C` is a bijection
(`Set.BijOn`) from `{Fa | IsFaceOf Ψ Fa C}` onto
`{X | IsAdmissibleType S X}`. Admissibility of face types is the existing
`isAdmissibleType_facetSimpleReflections`, injectivity is
`facetRel_of_fixingSimpleReflections_eq`, and surjectivity is the previous
result.

`subset_facetClosure_iff_facetSimpleReflections_subset`: for faces
`facet Ψ x`, `facet Ψ y` of `C`, the first lies in the closure of the second
exactly when the type of `y` is contained in the type of `x`.

## Scope

These results concern one chamber of an abstract affine root system, rank zero
allowed. They do not identify the generated subgroups with facet stabilizers,
compare types with parahoric subgroups, or concern any valuation quotient.
They prove no witness of `RootValuationBuildingConstructionStatement`.
