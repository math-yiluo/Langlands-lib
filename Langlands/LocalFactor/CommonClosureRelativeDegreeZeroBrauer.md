# Degree-zero Brauer induction relative to a normal subgroup of inertia, on actual Weil groups

Lean module: `Langlands.LocalFactor.CommonClosureRelativeDegreeZeroBrauer`.

## Source

P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981):

- Proof of Lemma 4.3, printed p. 109 (PDF p. 21). The constituents of the degree-zero
  virtual representation `W` are trivial on the ramification group `W(α(χ))`. The proof
  applies "la variante ([1], 1.5) du théorème de Brauer en dimension 0" and writes `W` as
  an integral combination of `Ind_H^W (X - 1)`. Here `H` is a subgroup of `W` containing
  `W(α(χ))`, and `X` is a quasi-character of `H` trivial on `W(α(χ))`.
- Proof of Lemma 4.7, printed pp. 110-111 (PDF pp. 22-23): "De la même manière qu'en
  4.4, on se ramène à supposer `W` de la forme `Ind_H^W (X - 1)`". This is the same step
  for the subgroup `W(α(χ)/2)`.

This module states and proves that step on the actual Weil subgroup
`W_E = weilSubgroup F E` of a finite intermediate field `E` of the common closure. The
ramification group is replaced by an arbitrary normal subgroup `N` of `W_E` contained in
inertia. The finite-group form is the Library's `FiniteRep.relativeDegreeZeroBrauer`
(`Langlands.Representation.Finite.RelativeDegreeZeroBrauer`).

## Definitions

- `relativeDegreeZeroInductionGenerators F E N : Set (Virtual F E)` is the set of classes
  `induce F E L h (characterClass η - characterClass 1)`. Here `L` is a finite
  intermediate field with `E ≤ L`, every element of `N` lies in `W_L`, and
  `η : W_L →ₜ* ℂˣ` is a continuous character with `η n = 1` for every `n ∈ N`. These are
  the actual common-closure inductions `Ind_{W_L}^{W_E} (η - 1)`.
- `weilTrivialOnSpan F E N : Submodule ℤ (Virtual F E)` is the integral span of the
  classes `ofRepresentation (ContinuousPredicate F E) ⟨A, hc⟩` of continuous finite
  representations `A` of `W_E` with `A.representation n = 1` for all `n ∈ N`.
- `WeilRelativeDegreeZeroBrauerStatement F : Prop` makes the following claim for every `E`
  and every normal subgroup `N` of `W_E` with `N ≤ CommonClosureWeilDeligne.inertia F E`.
  Every `x ∈ weilTrivialOnSpan F E N` with `x ∈ DegreeZero F E` lies in the integral span
  of `relativeDegreeZeroInductionGenerators F E N`.

  The formal statement expresses DH81's "the constituents of `W` are trivial on `N`" as
  membership in `weilTrivialOnSpan F E N`.

## Main theorem

`Langlands.LocalFactor.CommonClosure.weilRelativeDegreeZeroBrauer F :
WeilRelativeDegreeZeroBrauerStatement F`.

## Proof (as implemented)

Write `S_N` for the integral span of `relativeDegreeZeroInductionGenerators F E N`, and
`reducedClass x = x - degree x · [1]` (the Library's `Weil.reducedClass`).

1. **Reduction to single representations** (`weilRelativeDegreeZeroBrauer`). The map
   `reducedClass` is `ℤ`-linear and fixes degree-zero classes (`reducedClass_eq_self`).
   So it suffices to show `reducedClass [A] ∈ S_N` for every continuous `A` trivial on
   `N`.
2. **Composition series** (`reducedClass_mem_of_trivialOn`). The Library's
   `Weil.ExactCoefficients.series` is a composition series of `A` with irreducible
   graded pieces. `Weil.exactClass_eq_sum_of_filtration` writes `[A]` as the sum of their
   classes. Each graded piece is a quotient of a subrepresentation of `A`, so it is
   trivial on `N` (`eq_one_of_surjective_intertwiner` applied to the graded projection).
3. **Irreducible case** (`irreducible_reduced_mem`). The Library's
   `irreducible_finiteImage_unramifiedTwist` (from
   `Langlands.LocalFactor.CommonClosureAbelianNormalBrauer`) writes `A ≅ χ ⊗ B`. Here `B`
   is continuous with finite image and `χ` is trivial on inertia, hence on `N`. Through
   the equivalence `B` is trivial on `N`. `Weil.reducedClass_continuousTwist` gives
   `reducedClass [χ ⊗ B] = χ · reducedClass [B] + dim B · ([χ] - [1])`. The span `S_N` is
   stable under twisting by characters trivial on `N`
   (`continuousTwist_mem_relativeSpan`, via `continuousTwist_induce` and
   `continuousTwist_characterClass`). The class `[χ] - [1]` is a generator with
   `L = E` (`characterClass_sub_one_mem`, via `induce_self`).
4. **Finite-image case** (`finiteImage_sub_mem_relativeSpan`, `finiteImage_reduced_mem`).
   The kernel of `B` is open (`Weil.open_kernel_of_finite_range_of_closed`), and the
   quotient `Q = W_E ⧸ ker B` is finite. Then `B` descends to `ρ` on `Q` through
   `QuotientGroup.lift`. The finite class `[ρ] - dim B · [1]` lies in `trivialOnSpan Q (π N)`
   (`sub_mem_trivialOnSpan`, using `ofRepresentation_rho_eq_one` and
   `oneDimensional_one_rho`). It has degree zero (`sub_finrank_mem_degreeZero`). Its
   inflation along `π` is `[B] - dim B · [1]` (`inflate_ofClass`, `inflateEquiv`).
5. **Finite theorem and inflation** (`inflate_mem_relativeSpan`,
   `inflate_relativeGenerator_mem`). `FiniteRep.relativeDegreeZeroBrauer` puts the finite
   class into the span of `Ind_S^Q (χ' - 1)` with `π N ≤ S` and `χ'` trivial on `π N`.
   - `exists_galois_kernel` gives an open normal subgroup `U` of the Galois group whose
     preimage lies in `ker B`.
   - `exists_extension_of_le` identifies `π⁻¹ S` with `W_L` for a finite `L ⊇ E`.
   - `inflate_induce_oneDimensional_apply` sends `Ind_S χ'` to `induce F E L h [η]` with
     `η(w) = χ'(π w)`, and `Ind_S 1` to `induce F E L h [1]`.

   The subgroup `W_L` contains `N` because `π N ≤ S`. The character `η` is trivial on `N`
   because `χ'` is trivial on `π N`.

## Provenance

The statement is the Brauer step of DH81 4.3/4.7 (cited above) on the Library's actual
common-closure Weil subgroups. The ramification group `W(α)` is generalized to any normal
subgroup of inertia, and "constituents trivial on `N`" is expressed as membership in
`weilTrivialOnSpan F E N`. The proof is DH81's reduction: an irreducible representation
is the twist of a finite-image one by a character trivial on inertia, and the
finite-group variant is applied on a finite quotient. These helper statements are
internal to this proof:

- the twist-stability, irreducible and finite-image lemmas;
- the inflation lemmas;
- the finite-group lemmas `ofRepresentation_rho_eq_one`, `oneDimensional_one_rho`,
  `sub_mem_trivialOnSpan`, `sub_finrank_mem_degreeZero` and
  `eq_one_of_surjective_intertwiner`.

They reuse published Library constructions by Lean name.
