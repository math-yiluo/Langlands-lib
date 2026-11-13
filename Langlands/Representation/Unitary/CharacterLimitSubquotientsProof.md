# Proof: unitary constituents of an admissible character limit

Author: Worker 5667.

This module proves `Langlands.UnitaryCharacterLimitSubquotientsStatement.{uG, uV}`
(`Langlands/Representation/Unitary/CharacterLimitSubquotientsStatement.lean`).
The group universe `uG` and the carrier universe `uV` are independent.

The statement is a derived form of Tadić (1986), Theorem 2.7(i); see the statement's
Markdown for the source comparison. The implemented proof follows that Markdown's outline,
working one compact open subgroup at a time. It uses no compactness argument for the
sequence `π k`. Two hypotheses of the statement are not used: the irreducibility of the
`π k` and `SmoothRep.HasFiniteLength ρ` (they are bound as `_hirr` and `_hfin`). The proof
is split into a reduction lemma and the final theorem.

## Reduction lemma

`unitaryCharacterLimitSubquotients_of_cornerFormGluing (hglue : CornerFormGluingStatement.{uG, uV})`
proves the target from the gluing proposition `Langlands.CornerFormGluingStatement`. That
proposition says a smooth `ρ` is unitarizable when, for a compact open `K₀` with a nonzero
`K₀`-fixed vector, every fixed space `ρ^K` (`K ≤ K₀` compact open) is finite-dimensional,
simple over the Hecke corner `H_K`, and carries a positive definite Hermitian form for which
`star f` is adjoint to `f`.

Fix the data of the statement and an irreducible actual subquotient `τ` of `ρ`.

1. **Inversion invariance.** `μ` is a regular left Haar measure that is also right
   invariant, so `Langlands.isInvInvariant_of_isMulRightInvariant` makes it inversion
   invariant. This instance makes the corner `H_K` a `StarRing` and lets the positivity
   lemma below apply.
2. **Positivity of the limit character.** Each `π k` is admissible and unitarizable, so its
   character is of positive type (`Character.distribution_isPositiveType`): it is
   nonnegative on every `f† * f`. Positive type passes to pointwise limits
   (`Character.IsPositiveType.of_tendsto`), so the character of `ρ` is of positive type.
3. **Realizing the subquotient.** `SmoothRep.isSubquotient_iff_exists` gives a smooth `C`
   with an injective morphism `i : C → ρ` and a surjective morphism `q : C → τ`.
4. **A base level.** `τ` is irreducible, hence nonzero
   (`CharacterSeparation.nontrivial_of_isIrreducible`). Choose `v₀ ≠ 0`, an open subgroup `U`
   fixing it (smoothness), and a compact open `K₀ ≤ U`
   (`Hecke.TestFunction.commonCompactOpenBiInvariance` with the empty family). By
   `fixedVectors_antitone`, `v₀ ∈ τ^K` for every `K ≤ K₀`.
5. **Finite dimension.** `ρ^K` is finite-dimensional by admissibility (`hρ.2`). Then `C^K`
   is too, through the injection `fixedVectorsMap i` (`fixedVectorsMap_injective`). For
   compact `K`, `τ^K` is the image of `C^K` under `fixedVectorsMap q`, which is surjective by
   `fixedVectorsMap_surjective_of_complexAlgebra`.
6. **Simplicity.** For compact open `K ≤ K₀`, `τ^K ≠ 0` because it contains `v₀`.
   `CompactCoefficientClass.isSimpleModule_fixedVectors` (Bernstein–Zelevinsky 2.10) then
   makes `τ^K` a simple `H_K`-module.
7. **A form at each level.** Fix compact open `K ≤ K₀` with the corner module structures
   `Hecke.cornerModule` on `ρ^K`, `C^K` and `τ^K`.
   `CharacterLimitLevel.trace_cornerAction_star_mul_self_nonneg` turns step 2 into
   `0 ≤ trace (star a * a)` on `ρ^K` for all `a ∈ H_K`. `CharacterLimitLevel.cornerLinearMap`
   turns `i` and `q` into an injective `H_K`-linear map `C^K → ρ^K` and a surjective
   `H_K`-linear map `C^K → τ^K`. `PositiveTraceForms.exists_starInvariantForm_of_subquotient`
   gives a `StarInvariantForm H_K τ^K` `b`: a positive definite Hermitian form
   (`b.toInnerProductCore`) with `b(f • x, y) = b(x, star f • y)`. Its field `adjoint` is the
   required identity, because `f • x` is `cornerAction f x` by definition.
8. **Gluing.** Applying `hglue` to `τ`, `K₀`, `v₀` and steps 5–7 gives `IsUnitarizable τ`.

## Final theorem

`Langlands.unitaryCharacterLimitSubquotients : UnitaryCharacterLimitSubquotientsStatement.{uG, uV}`
is the reduction lemma applied to `Langlands.CornerFormGluing.cornerFormGluing`, Worker 4713's
published proof of `CornerFormGluingStatement.{uG, uV}`
(`Langlands/Representation/Unitary/CornerFormGluingProof.lean`, with the helper module
`CornerFormGluing.lean`). As its Markdown describes, that proof chooses a form at every level
`K ≤ K₀` and rescales it by a positive real so that `v₀` has norm `1`. For `L ≤ K ≤ K₀` the
pullback of the `L`-form to `ρ^K` is again corner-adjoint. Uniqueness of star-invariant forms on
a finite-dimensional simple module up to a positive scalar
(`PositiveTraceForms.StarInvariantForm.inner_mul_inner_eq`) and the normalization at `v₀` then
make the two forms equal on `ρ^K`. The compatible family glues to a positive definite Hermitian
form on the whole space. Its `G`-invariance follows from the adjoint identity applied to the
corner element `e_L ⋆ δ_g ⋆ e_L` (`translateCornerElement`) and its involution.

## Dependencies

- `Langlands.Representation.Unitary.CharacterLimitLevelInput`: level-wise trace positivity
  and corner-linear fixed-vector maps.
- `Langlands.LinearAlgebra.PositiveTraceForms` (Worker 5219): star-invariant forms on simple
  subquotients of a module with positive trace.
- `Langlands.Representation.Unitary.CornerFormGluingStatement` and its proof
  `Langlands.Representation.Unitary.CornerFormGluingProof` (Worker 4713).
- Published Library results named above (character positivity, subquotient realization,
  corner simplicity, fixed-vector maps, common compact open invariance, inversion invariance
  of a two-sided Haar measure).

## Validation

`lean_check` diagnostic `a0977658-1ceb-4eaa-9a9f-8f13644deb44` compiled this module against
Library `2e46b9ca` without errors or warnings. `Langlands.unitaryCharacterLimitSubquotients` has
universe parameters `uG, uV` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
