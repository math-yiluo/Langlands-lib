# A nonzero intertwiner from `PQ`-regularity

`exists_ne_zero_of_isPQRegular` is the algebraic step of Renard VII.3.4. Take represented
parabolics `P = MN` and `Q = MU` of a connected reductive `G` with the same Levi
(`l ≫ p = lQ ≫ q`), a split component `a : A → M`, and a nonzero smooth representation
`σ` of `M(F)` that is `PQ`-regular for `a` (`IsPQRegular`). Then some morphism
`i_P^G(σ) ⟶ i_Q^G(σ)` of smooth representations is nonzero. Here both inductions are
the published normalized represented inductions `leviInductionFunctor`. The provenance
is Renard, *Représentations des groupes réductifs p-adiques*, VII.3.4. The proof below
is the implemented Lean route.

## Proof

1. `pqSupportGraded` (Renard VII.3.2), part 2, supplies an equivariant linear equivalence
   `e σ : (F^{<1̄}/F^{≤1̄})(σ) ≃ σ`. Here `F^{<1̄} = boundarySupportImage 1̄` (the image
   of the functions vanishing on the boundary of the closure of `P 1̄ Q`) and
   `F^{≤1̄} = closureSupportImage 1̄` (the image of the functions vanishing on that whole
   closure) are the support filtrations of the Jacquet module of `i_P^G(σ)` along `Q` at
   the identity double coset, with `F^{≤1̄} ⊆ F^{<1̄}`. In the Lean proof the denominator
   is `S = F^{≤1̄}` and the numerator is `T = F^{<1̄}`.
2. Composing `e σ` with the quotient projection `S.quotientProjection T σ`, which maps
   `T(σ)` onto `T(σ)/S(σ)`, gives a surjective intertwiner `ψ : F^{<1̄}(σ) → σ` with
   domain `T(σ)`. Since `σ` is nontrivial, `ψ ≠ 0`.
3. `pqRegularIntertwiningRestrictionEquiv` applies under `PQ`-regularity. It composes
   Frobenius reciprocity (`leviFrobeniusReciprocity`) with restriction to `T = F^{<1̄}`, which
   is an equivalence by comaximality of the action kernels. The result is a linear
   equivalence `E` between intertwiners `i_P^G(σ) → i_Q^G(σ)` and intertwiners
   `F^{<1̄}(σ) → σ`.
4. The morphism `SmoothRep.ofHom (E.symm ψ)` is nonzero. If it were zero, then
   `E.symm ψ = 0`, so `ψ = E (E.symm ψ) = 0`, a contradiction.
