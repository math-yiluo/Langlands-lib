# Local invariants in towers of number fields and the Hasse principle for `H²(Eˣ)`

This module supplies the tower and Hasse-principle steps for the proof of the Library
proposition `Langlands.ClassField.Global.GlobalReciprocity` (statement module
`Langlands.ClassField.Global.ReciprocityStatement`, unchanged). That proof is Artin–Tate,
Theorem 6 of Chapter VII §3, and it belongs to global class field theory (task fb66219f).
This module proves no Library proposition by itself. It provides the following:

- local components of global classes in `H²(Gal(E/F), Eˣ)` commute with inflation and with
  restriction;
- the finite and archimedean local invariants, and the reciprocity law
  `SumOfInvariantsVanishes`, are unchanged by inflation;
- the Hasse principle: if `H¹(Gal(E/F), C_E) = 0`, a class of `H²(Gal(E/F), Eˣ)` whose local
  components all vanish is zero.

All declarations are in the namespace `Langlands.ClassField.Global.Reciprocity`. The only new
definitions are the four place-choice maps of section `PlaceChoices`. Everything else is a
theorem.

## Mathematical content and sources

Let `F ⊆ E ⊆ L` be number fields with `E / F` and `L / F` Galois, and let `u | w | v` be
places of `L`, `E`, `F`.

1. *Local components under inflation and restriction.* For `x ∈ H²(Gal(E/F), Eˣ)`, the local
   component of `Inf_L x` at `u` is the local inflation of the component of `x` at `w`. For
   an intermediate field `K` of `L / F` and `y ∈ H²(Gal(L/F), Lˣ)`, the component of
   `Res_K y` at `u` is the local restriction of the component of `y` at `u`. These are
   formulas (1) and (2) of Artin–Tate, *Class Field Theory*, Chapter VII §3, printed p.42
   (PDF p.51). Artin–Tate state them for idele classes `H²(G, J_K)`. Here they are stated for
   the composite `H²(Gal(E/F), Eˣ) → H²(Gal(E_w/F_v), E_wˣ)`, i.e. the Library map
   `unitsLocalMap`.
2. *Invariants under inflation.* Local invariants do not change under local inflation, so the
   invariant at `u` of `Inf_L x` equals the invariant of `x` at `w`. This is Lemma 1 of
   Artin–Tate VII §3, printed p.43 (PDF p.52). For finite places the local fact is the
   hypothesis `InflationCompatibility` on the invariant maps. At infinite places it is
   proved directly from the Library's explicit archimedean invariant (see `ArchimedeanTower`
   below).
3. *Reduction to a larger field.* Since every local invariant of `Inf_L x` equals one of `x`,
   `x` satisfies the reciprocity law iff `Inf_L x` does. The proof of Theorem 6 in Artin–Tate
   VII §3 uses this when it replaces `c` by its inflation to a larger normal field: printed
   p.45 (PDF p.54) and Case 3 on printed p.46 (PDF p.55).
4. *Hasse principle.* By `H¹(G, C_E) = 0`, the exact sequence
   `H¹(G, C_E) → H²(G, Eˣ) → H²(G, J_E)` makes `H²(G, Eˣ) → H²(G, J_E)` injective. A class of
   `H²(G, J_E)` is determined by its local components, so a class of `H²(G, Eˣ)` with all
   local components trivial is trivial. This is Theorem 2 of Artin–Tate, Chapter VI §1,
   printed p.19 (PDF p.28).

Provenance: derived. Some content is internal to this formalization:

- the cohomological equality `groupCohomology_map_congr`;
- the explicit archimedean computation;
- the place-choice maps;
- the description of "a class of `H²(G, J_E)` is determined by its local components". That
  step is the Library theorem `H2π_eq_zero_of_ideleLocalMap_eq_zero` of
  `IdeleLocalInjectivity`, together with `archimedeanIdeleInvariant_eq_zero_iff` of
  `IdeleArchimedean`.

## Sections and declarations

### `MapCongr`

- `groupCohomology_map_congr`: `groupCohomology.map f φ n = groupCohomology.map f' φ' n`
  when `f = f'` and `φ`, `φ'` agree pointwise.

### `Inflation`

Variables: number fields `F ⊆ E ⊆ L` with `IsScalarTower F E L`, `IsGalois F E` and
`IsGalois F L`. Finite places `v`, `w`, `u` of `F`, `E`, `L`, with instances
`w.asIdeal.LiesOver v.asIdeal`, `u.asIdeal.LiesOver w.asIdeal` and
`u.asIdeal.LiesOver v.asIdeal`.

- `relativeInflation_comp_unitsLocalMap` (morphism form) and
  `unitsLocalMap_relativeInflation (x : relativeCohomology F E 2)`:
  `(unitsLocalMap v u 2).hom ((relativeInflation F E L 2).hom x) =
  (relativeInflation (padicField v).Carrier (w.adicCompletion E) (u.adicCompletion L) 2).hom
  ((unitsLocalMap v w 2).hom x)`.
  Proof: both sides are `groupCohomology.map` of composites, by `groupCohomology.map_comp`.
  The group homomorphisms agree by the Library theorem
  `CompletionTower.decompositionHom_restrictNormal`. The coefficient maps agree because
  `E → L → L_u` and `E → E_w → L_u` coincide (`IsScalarTower`).
- `finiteLocalInvariant_relativeInflation (I) (hI : ∀ p [Fact p.Prime],
  (I p).InflationCompatibility) x`:
  `finiteLocalInvariant v u I ((relativeInflation F E L 2).hom x) =
  finiteLocalInvariant v w I x`. Proof: unfold `finiteLocalInvariant`, rewrite with
  `unitsLocalMap_relativeInflation`, then apply `hI` to the tower `L_u / E_w / F_v`.

### `Restriction`

Variables: number fields `F ⊆ K ⊆ L` with `IsScalarTower F K L` and `IsGalois F L`. `K` need
not be Galois over `F`. Places `u | w | v` as above. The statements contain
`haveI := IsGalois.tower_top_of_isGalois F K L`, which supplies `IsGalois K L` for
`relativeRestriction F K L`.

- `relativeRestriction_comp_unitsLocalMap` (morphism form) and
  `unitsLocalMap_relativeRestriction (y : relativeCohomology F L 2)`:
  `(unitsLocalMap w u 2).hom ((relativeRestriction F K L 2).hom y) =
  (relativeRestriction (padicField v).Carrier (w.adicCompletion K) (u.adicCompletion L)
  2).hom ((unitsLocalMap v u 2).hom y)`.
  Proof: the same composite argument. The group homomorphisms are compared after the
  injective map `L → L_u`, using `algebraMap_decompositionHom`. The coefficient maps agree by
  `rfl`.

### `ArchimedeanValue`, `ArchimedeanInflation`

These sections hold helper facts about the Library's `archimedeanCocycleHom` (statement
module `ReciprocityStatement`):

- `archimedeanCocycleHom_apply_of_exists` and `archimedeanCocycleHom_apply_of_not_exists`:
  unfold its `dite`;
- `archimedeanCocycleHom_apply_of_mem`: the value for any nontrivial `c` in the stabilizer.
  Two such `c` are both the complex conjugation at `w` (`IsConj.ext`);
- `archimedeanCocycleHom_apply_of_stabilizer_eq_bot`: value `0` at a place with trivial
  stabilizer;
- `signClass_conjugate`: `signClass` is invariant under complex conjugation;
- `isConj_comp_restrictNormal`: if `c'` is the conjugation of `φ : L →+* ℂ`, then its
  restriction to `E` is the conjugation of `φ ∘ (E → L)`;
- `conjugationValue_inflation`: the value `f(c,c) f(1,1)` of an inflated cocycle at `c'` is
  the image of the value of `f` at the restriction of `c'`.

### `PlaceChoices`

- `liesOver_of_comap_eq`, `liesOver_comap`: these move the `LiesOver` relation of infinite
  places along `E → L`.
- Definitions:
  - `liftFinitePlaces L wf`: above `v`, the place `placeAbove L (wf v)`.
  - `restrictFinitePlaces E wf'`: above `v`, the place `placeBelow E (wf' v)`.
  - `liftInfinitePlaces L wi`: above `v`, a chosen infinite place of `L` restricting to
    `wi v`, chosen through `InfinitePlace.comap_surjective`.
  - `restrictInfinitePlaces E wi'`: above `v`, the place `(wi' v).comap (algebraMap E L)`.
- `comap_liftInfinitePlaces`: the lifted infinite places restrict to the chosen ones.

### `ArchimedeanTower`

- `archimedeanInvariant_relativeInflation (u : InfinitePlace L) x`:
  `archimedeanInvariant u ((relativeInflation F E L 2).hom x) =
  archimedeanInvariant (u.comap (algebraMap E L)) x`.
  Proof: lift `x` to a cocycle `f` and compute both `H2Lift` values. Let `ψ` be `u`'s
  embedding restricted to `E`. Then `u.comap = mk ψ`.
  - If no nontrivial element fixes `u`, then `u` is unramified, hence so is its restriction
    (`IsUnramified.comap`). Both values are `0`.
  - If `c' ≠ 1` fixes `u`, the left side is `signClass(u(f(c̄,c̄) f(1,1)))`, where `c̄` is the
    restriction of `c'` to `E`.
    - If `c̄ = 1`, then `ψ` is real, the restricted place is unramified and the right side is
      `0`. The left side is `signClass(z̄ z) = 0` with `z = ψ(f(1,1))`, real.
    - If `c̄ ≠ 1`, then `c̄` fixes `mk ψ` and is its conjugation. The embedding of `mk ψ` is
      `ψ` or its conjugate, and `signClass_conjugate` handles the second case.
- `sumOfInvariantsVanishes_relativeInflation_iff (I) (hI : ∀ p [Fact p.Prime],
  (I p).InflationCompatibility) x`:
  `SumOfInvariantsVanishes I ((relativeInflation F E L 2).hom x) ↔
  SumOfInvariantsVanishes I x`.
  - (→) Given place choices `wf`, `wi` for `E`, apply the hypothesis to
    `liftFinitePlaces L wf` and `liftInfinitePlaces L wi`. By
    `finiteLocalInvariant_relativeInflation`, `archimedeanInvariant_relativeInflation` and
    `comap_liftInfinitePlaces`, the two families of invariants agree term by term.
  - (←) Symmetrically, with `restrictFinitePlaces E` and `restrictInfinitePlaces E`.

### `Hasse`

- `principalIdeleCohomologyMap_two_injective
  (hH1 : Subsingleton (relativeIdeleClassCohomology F E 1))`:
  `Function.Injective (principalIdeleCohomologyMap F E 2).hom`. Proof: exactness at
  `H²(Eˣ)` of the long exact sequence (`groupCohomology.mapShortComplex₁_exact`) of the
  Library short exact sequence `ideleCoefficientSequence_shortExact` `Eˣ → J_E → C_E`. The
  kernel is the image of `H¹(C_E) = 0`.
- `eq_zero_of_local_eq_zero (hH1 : IdeleClassH1Vanishing.{u}) (I)
  (hI : ∀ p [Fact p.Prime], (I p).RelativeImages) {F E} … (x : relativeCohomology F E 2)
  (hfin : ∀ v w [w.asIdeal.LiesOver v.asIdeal], (unitsLocalMap v w 2).hom x = 0)
  (hinf : ∀ w : InfinitePlace E, archimedeanInvariant w x = 0) : x = 0`.
  Proof: it suffices that the image `c` of `x` in `H²(G, J_E)` is `0`.
  1. By `archimedeanIdeleInvariant_principalIdeleCohomologyMap`, the archimedean idele
     invariants of `c` are those of `x`, all `0`. So `archimedeanIdeleInvariant_eq_zero_iff`
     gives a cocycle `f` representing `c` with trivial infinite components.
  2. `H2π_eq_zero_of_ideleLocalMap_eq_zero` then shows `c = 0`. It is applied with the places
     `placeAbove E v`; its local vanishing hypotheses come from `hfin` and
     `principalIdeleCohomologyMap_comp_ideleLocalMap`.
  3. Its finiteness and cardinality bounds for local `H²` come from the Library facts
     `relativeH2_finite` and `relativeH2_card` under `hI`.

  The hypotheses `I`, `hI` serve only these local bounds. Of `hH1`, only the instance at
  `E / F` is used.
