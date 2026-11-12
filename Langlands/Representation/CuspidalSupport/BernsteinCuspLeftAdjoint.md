# The functor `R` of Renard VI.7.2: exactness, finite type, faithfulness, injective units

Worker 4814. This is a supporting unit for Task 5419, which proves Renard VI.7.2,
second Lemma (`Langlands.CuspidalSupport.BernsteinCuspAdjunctionStatement`). It
proves the assertions about `R` in clause (ii), and clause (iii), for the actual
standard family (`BernsteinStandardFamily`). Two hypotheses stay explicit:

- every cuspidal-part functor `sc J` is a left adjoint of the inclusion of the
  cuspidal subcategory;
- for the exactness, faithfulness, finite-type and unit results, the cuspidal
  property of each standard Levi is split Serre (`SplitReflector.IsSplitSerre`).
  `isSplitSerre_cusp` reduces this to the existence of cuspidal/remainder
  splittings, which is what Renard VI.3.5 supplies.

The module does not prove clause (i), the statements about `I`, or the splittings.
It does not prove the target statement.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.7.2, second Lemma and its proof, printed pp.182–183 /
PDF pp.188–189; source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. These
pages were read. The three abbreviations reproduce the objects of the target
statement at an arbitrary carrier universe `uW`. The target uses
`uW = max uF uV`. The Lean proofs follow Renard's arguments, with the changes
noted below.

## Definitions

- `cusp family J`: the cuspidal representations of the literal standard Levi
  subgroup `levi i ν J`, meaning those whose proper standard normalized Jacquet
  modules inside `M_J` vanish (`Langlands.Aubert.General.IsLeviCuspidal` with the
  family's closedness and decomposition fields). For `uW = max uF uV` this is
  literally the target's `cusp J`.
- `jac family J`: the normalized Jacquet functor `jacquetFunctor` of the family's
  decomposition `P_J = M_J ⋉ N_J`. It is an abbreviation of the target's
  `normalizedJacquetFunctor (unipotent i ν J) (levi i ν J) …`.
- `bernsteinR family sc`: `Functor.pi' fun J => jac family J ⋙ sc J`, the
  target's `R` for a supplied family `sc`.

## Results and their proofs

- `isShortExact_id_id_iff`: `(𝟙 X, 𝟙 X)` is an actual short exact sequence if and
  only if `X` is zero, because the range of `𝟙 X` is everything and its kernel
  is zero. `subsingleton_obj`: so a functor that preserves actual short exact
  sequences sends zero objects to zero objects. Apply it to `(𝟙 X, 𝟙 X)` and use
  `Φ.map (𝟙 X) = 𝟙 (Φ X)`.
- `mono_map_of_adjunction`: a right adjoint preserves monomorphisms. Transport the
  equation through the inverse of the adjunction bijection and cancel.
- `unipotent_isLimitOfCompactSubgroups`, `jac_map_isShortExact`: the standard
  unipotent radicals are limits of compact subgroups (the published
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`,
  applied to the published `standardCocharacter` and the family's fields). So the
  published `jacquetFunctor_map_isShortExact` makes each `jac family J` exact.
- `isSplitSerre_cusp`: the cuspidal property is closed under injective
  intertwiners (`IsLeviCuspidal.of_isSubquotient`, with the inner unipotent radicals
  limits of compact subgroups by `isLimitOfCompactSubgroups_subgroupOf`) and under
  surjective intertwiners (`IsLeviCuspidal.of_surjective`). With supplied splittings
  it is split Serre.
- `bernsteinR_map_isShortExact`: the `J`-component of `R` is `jac family J`
  followed by `sc J`. The first is exact by `jac_map_isShortExact`, the second by
  `SplitReflector.map_isShortExact`. This is Renard's argument: the exactness of
  `r_P^G` together with the exactness of the projection to the cuspidal part.
  `bernsteinR_obj_subsingleton`: so every component of `R` sends zero objects to
  zero objects.
- `exists_nontrivial_bernsteinR_obj`: a nonzero `V` has a nonzero component of
  `R V`. This is the argument of Renard's proof of faithfulness. The published
  `exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier` takes a standard
  index `J` of minimal cardinality with nonzero Jacquet module, so that Jacquet
  module is cuspidal. Its inputs are the published proofs `standardCocharacter`,
  `standardLeviIntersection` and `relativeRootSystem`. The unit of `sc J` is
  injective at a cuspidal object (`SplitReflector.unit_injective_of_mem`), so
  `sc J (r_J V)` is nonzero.
- `bernsteinR_unit_injective` (clause (iii)): for every functor `I'` and every
  adjunction `R ⊣ I'`, every unit `V → I'(R V)` is injective. Renard's kernel
  argument, as implemented:
  1. Let `K ⊆ V` be the kernel of the unit, with inclusion `incl`.
  2. Each component of `R.map incl` is injective by componentwise exactness,
     applied to `0 → K → V → V/K → 0`. Hence `R.map incl` is a monomorphism
     componentwise, and therefore in the product category.
  3. `I'` preserves monomorphisms (`mono_map_of_adjunction`), so `I'(R(incl))` is
     injective. Naturality gives `I'(R(incl)) ∘ η_K = η_V ∘ incl = 0`, so the unit
     `η_K` at `K` vanishes.
  4. Renard concludes that `R(K) = 0` because `η_K` corresponds to the identity of
     `R(K)`. In the Lean proof, `η_K` factors through its image `D`, which is zero.
     So the identity of `R(K)` factors through `R(D)` (naturality of the
     adjunction bijection), and every component of `R(D)` is zero by
     `bernsteinR_obj_subsingleton`. Hence every component of `R(K)` is zero.
  5. `K = 0` by `exists_nontrivial_bernsteinR_obj`, so the unit is injective.

  Renard instead deduces `K = 0` from the faithfulness of `R`. Here the order is
  reversed: faithfulness is derived from (iii), so that no additivity of `R` is
  needed.
- `bernsteinR_faithful`: `R` is faithful whenever it has some right adjoint. Its
  units are monomorphisms by `bernsteinR_unit_injective` and the published
  `SmoothRep.mono_iff_injective`. Then Mathlib's
  `Adjunction.faithful_L_of_mono_unit_app` gives faithfulness.
- `bernsteinR_obj_finite`: if `V` is of finite type, every component of `R V` is of
  finite type. The Jacquet module is of finite type by the published
  `JacquetFiniteGeneration.finite_of_compactQuotient`, since `P_J \ G` is compact
  (`compactSpace_leftQuotient_parabolic` with the published
  `BruhatTits.dynamicParabolicQuotientCompact`; Renard VI.1.3). The unit of `sc J`
  is surjective (`SplitReflector.unit_surjective`), and Mathlib's
  `Module.Finite.of_surjective`, through
  `Representation.IntertwiningMap.equivLinearMapAsModule`, passes finite
  generation to the quotient.
