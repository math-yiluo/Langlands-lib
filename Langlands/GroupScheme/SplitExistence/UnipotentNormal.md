# Normal subgroups of unipotent matrices in `Γ(K)` are trivial

Module `Langlands.GroupScheme.SplitExistence.UnipotentNormal`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is the group-theoretic core of the
reductivity of the Chevalley group, for an infinite field `K`. The argument uses the BN-pair of
`Γ(K)` (modules `TitsTransfer` to `TitsFinal`). The statement and its proof are derived content;
compare the classical fact that the unipotent radical of a group with a split BN-pair is
trivial (Borel, *Linear Algebraic Groups*, §14).

## Declarations

- `IsBT M`: the `B`-shape. Every nonzero entry `(c, d)` of `M` is diagonal or has
  `ℓ(wt d) < ℓ(wt c)`.
- `IsBT.mul`: `B`-shaped matrices are closed under products. `IsBT.mul_apply_self`: on them,
  diagonal entries are multiplicative, `(M M')_cc = M_cc M'_cc`. A term `M_ce M'_ec` with
  `e ≠ c` would need both `ℓ(wt e) < ℓ(wt c)` and `ℓ(wt c) < ℓ(wt e)`.
- `isBT_one`, `IsBT.sub_one`, `IsBT.pow`, `IsBT.pow_apply_self`: closure under `1`, `M ↦ M - 1`
  and powers. The diagonal entries of `M ^ m` are `M_cc ^ m`.
- `IsBT.apply_self_eq_one`: if `M` is `B`-shaped and `(M - 1)ⁿ = 0`, then every diagonal entry
  of `M` is `1`, because `(M_cc - 1)ⁿ = 0` in a field.
- `isBT_of_mem_borelSub`: elements of `B(K) = T(K)·U⁺(K)` are `B`-shaped (`IsUT` for `U⁺`).
- `exists_units_pow_four_ne_one` (`K` infinite): some unit `t` has `t⁴ ≠ 1`, because
  `X⁴ - 1` has finitely many roots.
- `le_borelSub_of_unipotent` (`J` finite, `P` reduced, `K` infinite): **a subgroup `N ≤ Γ(K)`
  normalized by `Γ(K)` whose elements satisfy `(g - 1)ⁿ = 0` lies in `B(K)`.**
  `B·N = B ⊔ N` is a subgroup between `B` and `Γ ≤ B ⊔ N(T)`. If it contained no Weyl element
  `n_i`, parabolic rigidity (`IsConcreteTits.eq_of_le`) would give `B ⊔ N = B`, so `N ≤ B`.
  Otherwise write `n_i = b' u` with `b' ∈ B` and `u ∈ N`
  (`Subgroup.coe_mul_of_left_le_normalizer_right`). For a torus element `t = diag(χ(wt c))`,
  the commutator `u t u⁻¹ t⁻¹ = b'⁻¹ (n_i t n_i⁻¹) b' t⁻¹` lies in `N ∩ B`. Its diagonal is
  `χ(s_i(wt c)) / χ(wt c)`, and unipotence makes this `1`. Hence `χ ∘ s_i = χ` for every `χ`
  (`torusHom_injective`). For the coroot character `χ = α_i^∨(t)` evaluated at `α_i`, this
  says `t⁻² = t²`, i.e. `t⁴ = 1` for every unit `t`. That contradicts
  `exists_units_pow_four_ne_one`.
- `eq_bot_of_unipotent` (same hypotheses): **such a subgroup `N` is trivial.** By the previous
  lemma for `D` and for the opposite data `D.neg` (same `Γ`, functional `-ℓ`), `N ≤ B ∩ B⁻`.
  Matrices in both are block diagonal for the `ℓ`-grading (`borelSub_le_btSub` for `ℓ` and
  `-ℓ`), so `N ≤ T(K)` (`mem_torusSub_of_blockLevi`). A diagonal matrix with
  `(g - 1)ⁿ = 0` is `1`.
