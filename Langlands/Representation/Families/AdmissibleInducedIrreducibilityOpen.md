# Irreducibility neighborhoods for induced twists of admissible representations

Author: Worker 52. Module
`Langlands.Representation.Families.AdmissibleInducedIrreducibilityOpen`. The
main theorem is `Langlands.Renard.AlgebraicFamily.admissibleInducedIrreducibilityOpen`.
The helpers are in the namespace
`Langlands.Renard.AlgebraicFamily.AdmissibleInducedIrreducibilityOpen`. This is
internal support for the proof of `ConditionalParabolicGenericIrreducibilityStatement`.

## Source and scope

The source is Renard, *Représentations des groupes réductifs p-adiques*
(9 July 2026), VI.8.4 Proposition, printed p. 192 / PDF p. 198, with its proof
on printed pp. 192–193 / PDF pp. 198–199
(`renard-2026-representations-groupes-reductifs-padiques`). The proposition
says: let `P = MN` be parabolic, `ρ` an irreducible smooth representation of
`M`, and `ψ₀` an unramified character such that `i_P^G(ρ ⊗ ψ₀)` is irreducible.
Then `i_P^G(ρ ⊗ ψ)` is irreducible for every `ψ` in a Zariski open
neighborhood of `ψ₀`. The Library formalizes it as
`Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement`.

`admissibleInducedIrreducibilityOpen` proves that conclusion verbatim for every
`ρ` that is irreducible **and admissible**. The extra hypothesis
`ρ.IsAdmissible` is the only difference from one instance of
`InducedIrreducibilityOpenStatement`. Jacquet's theorem would remove this
hypothesis, since it makes every irreducible smooth representation admissible,
but that theorem is not used here. The proof of the generic-irreducibility
target needs only admissible `ρ`. The binders and conclusion are exactly those of the Library statement:
`k`, `G`, `hG`, the point topology instances, `P M U p l r hp hl hr hmul`, the
Levi point topology `leviPointTopology l hl`, `ρ : SmoothRep.{0, u, v} ℂ M(k)`,
`hρ : ρ.IsIrreducible`, `hadm : ρ.IsAdmissible`, `ψ₀`, and irreducibility of
`(leviInductionFunctor p l r hp hr hl hmul).obj (ρ.twist ψ₀ …)`. The conclusion
is `∃ f : MvPolynomial (Fin (rationalImageRank M)) ℂ`, with `ψ₀` in
`rationalUnramifiedPrincipalOpen M _ f`, such that the induced twist is
irreducible at every `ψ` in that principal open set.

## Proof route

The source proof uses a compact open `K` that detects every irreducible
subquotient of every `i_P^G(ρ ⊗ ψ)`. This module proves only the weaker
detection `IsSubrepDetected` of `SubrepDetectionPrincipalOpen`, for one `K` and
every `ψ`. It then applies
`exists_polynomial_principal_neighborhood_of_family_of_subrepDetected` to the
published universal family `ActualLevi.universalFamily`. That family is a global
coefficient family by
`InducedIrreducibilityOpenAssembly.universalFamily_isGlobalCoefficientFamily`.
The proof does not use second adjointness or a joint special compact basis.

### Helpers

- `hom_injective_of_iso`: the underlying map of an isomorphism of smooth
  representations is injective.
- `leviInduction_subrep_exists_fixed` (Frobenius reciprocity and the weak
  Jacquet lemma). Hypotheses:
  - `K` is a compact open subgroup of `G(k)` with an Iwahori contraction
    `Jacquet.IsIwahoriContraction K N(k) M(k) X g`;
  - `C` is a compact open subgroup of `M(k)` containing every Levi point that
    lies in `K`;
  - `σ` is irreducible with a nonzero `C`-fixed vector;
  - `(i_P^G σ)^K` is finite dimensional.

  Then every nonzero subrepresentation `W` of `i_P^G σ` has a nonzero `K`-fixed
  vector. Proof: the inclusion `W → i_P^G σ` is nonzero. Its adjoint
  `J(W) → σ`, under the published `leviFirstAdjointnessAdjunction`, is nonzero
  (exactness from `leviParabolicFunctorsExact`), so surjective because `σ` is
  irreducible. `Compact.fixedVectorSurjectivity` lifts the `C`-fixed vector to a
  nonzero `C`-fixed vector of `J(W)`. That vector is fixed by the Levi points in
  `K`. The published weak Jacquet lemma `exists_fixed_of_normalizedJacquet_fixed`
  then gives a nonzero `K`-fixed vector of `W`. `W^K` is finite dimensional
  because it injects into `(i_P^G σ)^K`. The inducing representation lives in
  carrier universe `max u v`, as the adjunction requires.
- `leviInduction_fixedVectors_generate_of_admissible`: under the same
  hypotheses, with `σ` admissible, a subrepresentation `S` containing
  `(i_P^G σ)^K` is everything. Suppose `S ≠ ⊤`. The quotient `Q = i_P^G σ / S`
  has no nonzero `K`-fixed vector (fixed vectors lift by
  `Compact.fixedVectorSurjectivity`), so its contragredient has none
  (`contragredient_fixed_eq_zero`). `Q` is nonzero, so `Q~` is nonzero
  (`exists_contragredient_fixed_ne_zero`). `Q~` embeds into
  `(i_P^G σ)~ ≅ i_P^G(σ~)`, by `contragredientMap_injective_of_surjective` and
  `nonempty_leviInductionContragredientIso`. Its image is a nonzero
  subrepresentation of `i_P^G(σ~)`. Moreover:
  - `σ~` is irreducible and admissible (`SmoothRep.isIrreducible_contragredient_iff`,
    `isAdmissible_contragredient_iff`);
  - `σ~` has a nonzero `C`-fixed vector;
  - `(i_P^G σ~)^K` is finite dimensional by `leviInductionFunctor_obj_isAdmissible`
    and the published `arbitraryParabolicQuotientCompact`.

  So the previous helper gives a nonzero `K`-fixed vector in the image. Its
  preimage is a nonzero `K`-fixed vector of `Q~`, a contradiction.
- `leviInduction_subrepDetected_of_universeLift`: detection of the induction of
  `SmoothRep.universeLift τ` gives detection of the induction of `τ`. This uses
  `normalizedInductionEquivOfEquiv` and `IsSubrepDetected.of_equiv`.
- `exists_uniform_subrepDetected`: for irreducible admissible `ρ` there is one
  compact open `K` with `IsSubrepDetected` for every `i_P^G(ρ ⊗ ψ)`. Proof:
  1. Fix a nonzero `v₀ ∈ ρ` and a compact open `Cρ ⊆ M(k)` fixing it.
  2. Choose an open `O ∋ 1` of `G(k)` whose Levi points lie in `Cρ`.
  3. The published `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`,
     `pointImage_radical_eq_dynamic` and
     `RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis` give a
     compact open `K ⊆ O` with an Iwahori contraction relative to `P = MN`
     itself.
  4. Every unramified `ψ` is trivial on `Cρ`
     (`compactSubgroup_le_rationalCommonNormKernel`), so `v₀` stays `Cρ`-fixed
     in `ρ ⊗ ψ`. Twisting and universe lifting preserve irreducibility and
     admissibility.
  5. The two helpers give detection, and the universe-lift helper transports it
     back.

### Main theorem

`admissibleInducedIrreducibilityOpen` takes `K` from
`exists_uniform_subrepDetected`. It then applies
`exists_polynomial_principal_neighborhood_of_family_of_subrepDetected` to
`ActualLevi.universalFamily p l r hp hl hr hmul ρ`, with the coefficient
algebra identification `(ActualLevi.regularAlgebraEquiv p l hp hl).symm`.

## Checks

The module compiles with zero errors and zero warnings in the environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.
