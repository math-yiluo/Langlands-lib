# The Hom bound for standard cuspidal data of a standard family

Module `Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalHomBoundFamily`,
namespace `Langlands.CuspidalSupport.HomBound`.

## Purpose and provenance

This module specializes the rational-level Hom bound of
`Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalHomBound` to the
actual standard cuspidal data of a `BernsteinStandardFamily`. These are the
objects of the published target
`Langlands.CuspidalSupport.BernsteinSupercuspidalInductionBoundsStatement`
(Renard, *Représentations des groupes réductifs p-adiques* (2026), VI.5.4,
Theorem, printed pp. 173–174 / PDF pp. 179–180, second bound).

The result is the bound by **minimal double-coset representatives** lying in
Renard's set `W(ρ, ρ')`. The target counts the left cosets `w W_M` of
`W(ρ, ρ')` instead. Turning one count into the other is a separate
group-theoretic step: each minimal representative of `W_{M'} \ W / W_M` in
`W(ρ, ρ')` is determined by its coset `w W_M`. That step is not part of this
module. The module is derived infrastructure with one non-proved input, the
proper-standard exclusion `PointLeviStandardInductionCuspidalExclusion`. The
second theorem takes it from the published
`RationalCuspidalExtractionInputsStatement`.

## Definition

`bernsteinMatchingWeyl i ν family a a' : Set (Weyl i)`, for standard cuspidal
data `a = (M, ρ)` and `a' = (M', ρ')` (`BernsteinCuspidalDatum`), is the set of
`w ∈ W_G = N_G(A_∅)/Z_G(A_∅)` having a representative `n` in the actual
normalizer of the torus points such that

* `h : n M n⁻¹ = M'`, written `(levi i ν a.roots).map (MulAut.conj n) = levi i ν a'.roots`;
* there is a linear equivalence `e` from the carrier of `ρ` to the carrier of
  `ρ'` (literal Levi representations `bernsteinLiteralLeviRep`) with
  `e (ρ(m) x) = ρ'(n m n⁻¹) (e x)` for all `m ∈ M(F)`. Here `n m n⁻¹` is
  `Group.RelativeWeyl.conjugationEquiv n M M' h m`. That is,
  `ρ' ∘ Ad(n) ≃ ρ` as representations of `M(F)`.

This is Renard's `W(ρ, ρ')` (VI.5.4). It is word for word the set whose image in
`W_G / W_M` appears in the second conjunct of
`BernsteinSupercuspidalInductionBoundsStatement`, so the definition introduces
no new mathematical choice.

## Theorems

* `bernsteinInduction_rank_intertwiningMap_le_card_minimal`: assume an
  injective torus embedding `[Mono i.hom.hom.left]`, a finite enumeration of the
  simple roots, the point normalizer and centralizer comparisons `hN`, `hZ`, an
  actual point Coxeter system `cs` with the standard-Levi Weyl identification
  `hIdent` and the root-length comparison `hLength`, and the exclusion input
  `hExclude`. Then, for standard cuspidal data `a` and `a'`,

  `rank Hom_G(bernsteinInduction a, bernsteinInduction a') ≤
    Nat.card {w // IsMinimal cs a'.roots a.roots w ∧ w ∈ bernsteinMatchingWeyl a a'}`.

  Here `IsMinimal cs J I w` says `w` has minimal length in `W_J w W_I`.

* `bernsteinInduction_rank_intertwiningMap_le_card_minimal_of_inputs`: the same
  bound with `hExclude` taken from
  `hInputs : RationalCuspidalExtractionInputsStatement.{uF, uV}`. It uses the
  enumeration `simpleRelativeRootFintype` of that statement and the proved
  standard-cocharacter, standard-Levi-intersection and relative-root-system
  inputs.

## Proof

The induced representations of the family carry `Type (max uF uV)`. The
rational-level theorem `rank_normalizedInduction_intertwiningMap_le` needs
Levi representations on `Type (max (uF+1) uV)`. So the proof lifts the literal
Levi representations `ρ`, `ρ'` with `SmoothRep.universeLift.{uF+1}`, keeping
the action pointwise:

1. Irreducibility of the literal representations comes from irreducibility of
   the scheme-point representations by pulling back along
   `leviRationalPointHomeomorph`. It passes to the lifts by
   `isIrreducible_universeLift_iff`.
2. Inside-Levi cuspidality passes to the lifts by
   `IsCuspidalFor.of_surjective_intertwiner` along the lift equivalence.
3. The predicate `P w := w ∈ bernsteinMatchingWeyl a a'` satisfies the
   hypothesis of the rational theorem. An isomorphism `ⁿ(ρ↑) ≅ ρ'↑` yields
   `n M n⁻¹ = M'` and the required linear equivalence `e` by
   `exists_conjugation_linearEquiv_of_iso_universeLift`.
4. The rational theorem bounds `rank Hom(i(ρ↑), i(ρ'↑))`. The Hom spaces
   before and after lifting are linearly equivalent by
   `intertwiningMapLinearCongr` of the published
   `normalizedInductionUniverseLiftEquiv`. `LinearEquiv.lift_rank_eq` and
   `Cardinal.lift_le_nat_iff` then transfer the bound.

The family's decompositions (`family.decomposition`,
`family.leviDecomposition`) and the standard-cocharacter decompositions used at
the rational level are proofs of the same propositions, so they agree
definitionally. The ambient topology is the family's point topology. It is
Hausdorff by `rationalPoint_t2Space`, using that the local field is Hausdorff
(`GeneralLocalField.t2Space`). The Weyl group is finite by
`exists_rootSpanPointCoxeterSystem`.
