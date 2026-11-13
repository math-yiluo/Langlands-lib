# The Hom bound for induction from cuspidal data (rational level)

Module `Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalHomBound`,
namespace `Langlands.CuspidalSupport.HomBound`.

## Purpose and provenance

This module proves the representation-theoretic half of the second bound of
Renard, *Représentations des groupes réductifs p-adiques* (2026), VI.5.4,
Theorem (printed pp. 173–174 / PDF pp. 179–180):

`dim Hom_G(i_P^G(ρ), i_{P'}^G(ρ'))` is bounded by a count of Weyl elements.

Renard's proof applies Frobenius reciprocity (first adjointness),
`Hom_G(i_P^G ρ, i_{P'}^G ρ') = Hom_{M'}(r_{P'}^G i_P^G ρ, ρ')`, and then the
geometric lemma, which filters `r_{P'} i_P ρ` by pieces indexed by double cosets
`W_{M'} \ W / W_M`. A piece contributes only when its Weyl element `w` satisfies
`w · M = M'` and `ρ' ∘ Ad(w) ≃ ρ`, and then it contributes at most one dimension
(Schur's lemma). This module formalizes that argument for the actual standard
data of the rational-point family. It gives the bound by **minimal double-coset
representatives** satisfying an arbitrary predicate `P`. The passage to the
coset count `|W_M \ W(ρ, ρ')|` of the target statement is the separate,
purely group-theoretic comparison of Weyl cosets.

The module is internal (derived) infrastructure. It adds no new definition of
mathematical objects beyond the linear isomorphism `intertwiningMapLinearCongr`.
It takes one non-proved input, the proper-standard exclusion
`PointLeviStandardInductionCuspidalExclusion` (published in
`Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs`). It
is the second conjunct of the published `RationalCuspidalExtractionInputsStatement`.
It says that a proper standard induction inside a standard Levi has no
irreducible cuspidal subquotient. It is needed only for the geometric pieces
where the source Levi is fully conjugated into a proper part of the target.

## Generic lemmas

* `intertwiningMapLinearCongr e₁ e₂`: representation equivalences
  `e₁ : ρ ≃ ρ'` and `e₂ : τ ≃ τ'` (carriers in four independent universes)
  give a linear equivalence `Hom(ρ, τ) ≃ₗ Hom(ρ', τ')`, `f ↦ e₂ ∘ f ∘ e₁⁻¹`.
* `rank_le_zero_of_forall_eq_zero`, `rank_intertwiningMap_le_of_iso`: rank
  bookkeeping for vanishing intertwiner spaces and isomorphic sources.
* `map_conj_eq_of_forall_mem_iff`: `x ∈ L' ↔ g⁻¹ x g ∈ L` for all `x` implies
  `g L g⁻¹ = L'` (as `Subgroup.map (MulAut.conj g)`).
* `sum_ite_enumeration_eq_card`: summing the indicator of `P` along an
  enumeration `Fin n ≃ {w // Q w}` gives `Nat.card {w // Q w ∧ P w}`.
* `rank_intertwiningMap_le_one` (Schur): between a smooth irreducible
  representation of a separable topological group and an irreducible
  representation there is at most one independent intertwiner. It uses the
  published `Schur.separableSmoothEndomorphismEquiv`.
* `intertwiningMap_eq_zero_of_not_isSubquotient`: an intertwiner to an
  irreducible `τ` vanishes when `τ` is not a subquotient of the source.
* `rank_intertwiningMap_le_ite`: if either `τ` is not a subquotient of `X`, or
  `X ≅ Y` with `Y` irreducible and `Y ≅ τ` forcing a proposition `p`, then
  `rank Hom(X, τ) ≤ if p then 1 else 0`.
* `rank_intertwiningMap_le_ite_of_conjugate`: the same with `Y` the conjugate
  `ᵍσ` (`conjugationFunctor`) of an irreducible `σ`.
* `conjugationEquiv_relativeWeylConjugationEquiv` and
  `exists_conjugation_linearEquiv_of_iso_universeLift`: an isomorphism
  `ᵍ(A↑) ≅ B↑` between universe lifts gives `g L g⁻¹ = L'` and a linear
  equivalence `e : A ≃ B` with `e (A m x) = B (g m g⁻¹) (e x)` for `m ∈ L`.
  This is exactly the shape of the representation-equivalence witness in the
  target statement's set `W(ρ, ρ')`.

## Rational-point results

Context: the actual rational-point family (`k` a field with a topology,
`RationalPoint k G.X` with the canonical point topology, standard parabolics
`parabolic i ν I`, Levis `levi i ν I`, unipotent radicals `unipotent i ν I`). It
also uses an actual point Coxeter system `cs` with Weyl group `Weyl i`.

* `rank_geometricTerm_intertwiningMap_le`: for irreducible inside-Levi cuspidal
  `σ` on `M_I` and `τ` on `M_J`, one actual geometric term of `r_J i_I σ` at a
  minimal representative `w` with lift `m` has
  `rank Hom(term, τ) ≤ if P w then 1 else 0`. Here `P` is any predicate such
  that every normalizer element `n` with `ⁿσ ≅ τ` has `P (class of n)`. The
  proof instantiates the published grade dichotomy
  `PointGeometricCuspidalGradeDichotomy`: either the term has no irreducible
  inside-Levi cuspidal subquotient, or it is isomorphic to the conjugate `ᵐσ`.
* `rank_pointInducedJacquet_intertwiningMap_le`: summing over the published
  actual geometric filtration `PointGeometricObjectFiltration` of `r_J i_I σ`,
  whose grades are enumerated bijectively by the minimal representatives,
  `rank Hom(r_J i_I σ, τ) ≤ Nat.card {w // IsMinimal cs J I w ∧ P w}`. It uses
  the published `ObjectRepFiltration.rank_intertwiningMap_le_sum`.
* `rank_normalizedInduction_intertwiningMap_le` (main result): over a
  nonarchimedean local field, given the relative root system, the
  standard-Levi Weyl identification `hIdent`, the root-length comparison
  `hLength` and the exclusion input `hExclude`, then
  `rank Hom_G(i_I σ, i_J τ) ≤ Nat.card {w // IsMinimal cs J I w ∧ P w}`.
  Here `IsMinimal cs J I w` says `w` has minimal length in `W_J w W_I`. The
  proof rewrites by the published first adjointness
  `RationalPointFamily.FirstAdjointness.equiv`. It builds the grade
  dichotomy from `pointCuspidalExtractionGeometry_of_rootComparisons` and
  `pointProperTargetGeometricTermExclusion_of_standardInduction`, and the
  filtration from `pointGeometricObjectFiltrationOfEpsilonBalance` with the
  proved Haar balance `geometricEpsilon_mul_eq_one`. It then applies the
  previous bound.
