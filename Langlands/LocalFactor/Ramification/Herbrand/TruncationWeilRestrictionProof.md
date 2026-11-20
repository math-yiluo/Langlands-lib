# Restriction of Weil representations at a transitivity index

`Langlands.Ramification.Kummer.truncationWeilRestriction` proves
`TruncationWeilRestrictionStatement.{u, v}`. Let `F` be p-adic, `E` a finite
intermediate extension, and `μ ≥ -1` an index satisfying
`E.field.fixingSubgroup ⊔ G_F^μ = ⊤`. Write `W_E` for the Weil group of
`E.asPadicField` and `R_F(r)`, `R_E(r)` for the Weil upper groups. The proof
formalizes the representation consequence of the filtered quotient in
Lemma `lem:trunc` of the operator route note
`operator-numerical-llc-route-2026-11-16`, lines 876–889, in the formulation of
the [published statement](TruncationQuotientStatement.md).

## The quotient action

Let `q_F` and `q_E` be the quotient maps by `R_F(μ)` and `R_E(μ)`,
respectively, and let `ι = (intermediateWeilMap F E).toMonoidHom`.
`truncationWeilQuotient` at `μ` gives a continuous multiplicative equivalence
`φ : W_E/R_E(μ) ≃ₜ* W_F/R_F(μ)` with `φ ∘ q_E = q_F ∘ ι`. In particular,
`q_F ∘ ι` is surjective because `q_E` and `φ` are surjective. The equivalence
also identifies the images of the upper groups through `μ`.

The private definition `descendToWeilQuotient` uses `QuotientGroup.lift` to
factor an action trivial at `μ` through its Weil quotient on the original
vector space. Composing the descended action with the quotient map recovers
the original action. The helper `descendToWeilQuotient_isContinuous` applies
`QuotientGroup.isQuotientMap_mk` to deduce continuity of the descended action
from continuity of that composite.

## Bijection on continuous isomorphism classes

- Restriction preserves continuity by `weilRestrict_isContinuous`. If
  `w ∈ R_E(μ)`, then `q_E(w) = 1`, so `q_F(ι(w)) = φ(1) = 1` and
  `ι(w) ∈ R_F(μ)`. Thus the restriction is trivial at `μ`.
- If two restricted representatives are isomorphic, use the linear
  equivalence of the given intertwiner. For any `w ∈ W_F`, choose
  `w' ∈ W_E` with `q_F(ι(w')) = q_F(w)`. Both original actions factor
  through `q_F`, so the intertwining relation at `w'` for their
  restrictions gives the relation at `w` for the original actions.
  `FiniteRepresentation.classOf_eq_iff` turns this equivalence into
  equality of the original classes.
- For a continuous representative of a target class, descend its action to
  `W_E/R_E(μ)` and pull back along `φ⁻¹ ∘ q_F`. This pullback is continuous
  and trivial on `R_F(μ)`. Since `(φ⁻¹ ∘ q_F) ∘ ι = q_E`, its restriction
  recovers the given representative.

## Irreducibility and upper fixed spaces

For any representation `A` trivial on `R_F(μ)`, the original action and
its restriction are pullbacks of the same quotient action along the
surjections `q_F` and `q_F ∘ ι`. Applying
`FiniteRepresentation.isIrreducible_restrict_iff` to each gives the
irreducibility equivalence under this triviality hypothesis.

For `-1 ≤ r ≤ μ`, the filtration clause of `truncationWeilQuotient` gives
`(q_F ∘ ι)(R_E(r)) = q_F(R_F(r))` as sets in `W_F/R_F(μ)`.
`mem_upperFixedSpace` and `Set.forall_mem_image` express the two fixed-space
membership conditions as being fixed by every element of this common
image under the quotient action. The fixed submodules are therefore equal
on the shared carrier. For `r > μ`, antitonicity gives triviality at `r`
on each side by `isTrivialAt_mono`, so both fixed submodules are the whole
carrier. Applying `Module.finrank ℂ` to the equality yields the rank
comparison for every `r ≥ -1`.
