# Local compatibility of global invariants from the total idele invariant

Author: Worker 226.

Exact statement interface documentation: Worker 369 and Worker 226.

This module proves the published statement
[InvariantLocalFromTotalStatement](InvariantLocalFromTotalStatement.md):

- `Langlands.ClassField.Global.globalInvariantLocalFromTotalStatement :
  GlobalInvariantLocalFromTotalStatement.{u}`.

Take global invariant maps `inv` that satisfy the image law `InvariantImages inv` and the
class-level restriction law `InvariantRestrictionOnClasses inv`, and that agree with every total
idele invariant (`InvariantTotalAgreement I hI inv`). Then `inv` is locally compatible with
the local family `I` (`InvariantLocalOnClasses I inv`). The statement, its hypotheses and all
imported definitions are unchanged. Besides the statement module, the module imports
[IdeleTotalSection](IdeleTotalSection.md) and Worker 269's
[DecompositionField](DecompositionField.md). It adds no axioms. Its only instance is the
additivity of group cohomology in the coefficients, described below.

## Corestriction (namespace `Langlands.Shapiro`)

Let `k` be a commutative ring and `φ : H →* G` a homomorphism of groups in `Type u` such that
`G ⧸ φ.range` is finite. The Library module [IdeleSemilocal](IdeleSemilocal.md) provides the
Shapiro map `shapiroMapOf`, the Shapiro isomorphism `shapiroIsoOf hφ` (for injective `φ`) and
the coset sum `coindSum φ ι : Coind_φ A ⟶ B`, `f ↦ ∑_{x φ(H)} x • ι (f x⁻¹)`.

- `groupCohomology_functor_additive` (an instance): the functor `groupCohomology.functor k G n`
  is additive. The map induced on `Hⁿ` by `f + g` is the sum of the induced maps, by Mathlib's
  `HomologicalComplex.homologyMap_add`.
- `map_id_nsmul`: the map induced by `m • f` is `m •` the map induced by `f`.
- `resCoindToHom_comp_coindSum_id`: the morphism `B ⟶ Coind_φ (Res_φ B)` adjoint to the
  identity, followed by the coset sum of the identity, is `[G : φ(H)] • 𝟙 B`. Indeed
  `∑_{x φ(H)} x • (x⁻¹ • b) = [G : φ(H)] • b`.
- `coindSum_eq_coindMap_comp`: the coset sum of `ι : A ⟶ Res_φ B` is the coinduced map
  `Rep.coindMap φ ι` followed by the coset sum of the identity of `Res_φ B`.
- `coindSum_comp`: a coset sum followed by `π : B ⟶ B'` is the coset sum of `ι` followed by the
  restriction of `π`.
- `map_coindMap_comp_shapiroMapOf`: the Shapiro map is natural in the coefficients.
- `shapiroCor hφ B n : Hⁿ(H, Res_φ B) ⟶ Hⁿ(G, B)`, for injective `φ`, is the inverse Shapiro
  isomorphism followed by the map induced by the coset sum of the identity of `Res_φ B`. This
  is the corestriction in Milne's description (*Class Field Theory*, v4.03, 2020, Chapter II,
  Example 1.29, printed p.70, PDF p.79): Shapiro's isomorphism followed by the map induced by
  `φ ↦ ∑_s s φ(s⁻¹)`.
- `map_comp_shapiroCor` and its form on classes `shapiroCor_map`: restriction along `φ`
  followed by `shapiroCor` is multiplication by `Fintype.card (G ⧸ φ.range)`. This is Milne's
  Proposition 1.30 (same page). The proof factors restriction as the map induced by the
  adjoint of the identity followed by the Shapiro map (the Library's
  `map_resCoindToHom_comp_shapiroMapOf`). The Shapiro isomorphism then cancels, and
  `resCoindToHom_comp_coindSum_id` with `map_id_nsmul` gives the result.
- `shapiroIsoOf_inv_map_coindSum`: for `ι : A ⟶ Res_φ B`, the inverse Shapiro isomorphism for
  `A` followed by the map induced by `coindSum φ ι` equals the map induced by `ι` on
  `Hⁿ(H, -)` followed by `shapiroCor`. The proof uses `coindSum_eq_coindMap_comp` and the
  naturality of the Shapiro map.

## The corestriction from the decomposition group

The remaining declarations are in namespace `Langlands.ClassField.Global`. Let `F, E` be
number fields with `E / F` normal, and let `w ∣ v` be finite places. The decomposition group
`Gal(E_w/F_v)` acts on `C_E` through `decompositionHom v w`.

- `ideleLocalEmbedding_comp_ideleQuotientCoefficients`: the single-coordinate embedding
  `E_wˣ → J_E` followed by the quotient `J_E → C_E` is the single-coordinate map
  `localIdeleClassCoefficients v w` into `C_E`. The two sides agree by definition.
- `decompositionCorestriction v w n`, an abbreviation, is `shapiroCor` for the injective
  decomposition map with coefficients `C_E`:
  `Hⁿ(Gal(E_w/F_v), C_E) ⟶ Hⁿ(Gal(E/F), C_E)`.
- `ideleLocalSection_comp_ideleQuotientCohomologyMap`: the Library's finite local section
  `ideleLocalSection v w n : Hⁿ(Gal(E_w/F_v), E_wˣ) ⟶ Hⁿ(Gal(E/F), J_E)` followed by the
  quotient map to `Hⁿ(Gal(E/F), C_E)` equals `localIdeleClassMap v w n` followed by
  `decompositionCorestriction v w n`. The local section is the inverse Shapiro isomorphism
  followed by the coset sum of the single-coordinate embedding. So the identity follows from
  `coindSum_comp`, the previous lemma and `shapiroIsoOf_inv_map_coindSum`.
- `decompositionCorestriction_decompositionRestriction`: `decompositionRestriction v w n`
  followed by `decompositionCorestriction v w n` is multiplication by the index of
  `Gal(E_w/F_v)` in `Gal(E/F)`.

## The invariant argument

- `exists_nsmul_eq_of_nsmul_eq_zero`: in `ℚ/ℤ`, if `k ≠ 0` and `m • z = 0`, then `z = k • x`
  for some `x` with `(k * m) • x = 0`. Take `x` to be the class of `q / k`, where `q` is a
  rational representative of `z`.
- `relativeIdeleClassRestriction_surjective`: assume `InvariantImages inv` and
  `InvariantRestrictionOnClasses inv`, let `E / F` be Galois and let `F'` be a number field
  in a tower `F → F' → E`. Then restriction
  `H²(Gal(E/F), C_E) → H²(Gal(E/F'), C_E)` is surjective. Proof: the invariant of a class `y`
  of `E / F'` is killed by `[E : F']`. By the previous lemma it is `[F' : F] • x` with `x`
  killed by `[E : F]`. By the image law for `E / F`, `x = inv F E a` for some `a`. By the
  restriction law, `inv F' E (Res a) = [F' : F] • x = inv F' E y`, so `Res a = y` because
  `inv F' E` is injective.

In the rest of this section, `inv` agrees with every total idele invariant for the local
family `I` (with witnesses `hI`). Let `w ∣ v` be finite places of a Galois extension `E / F`.

- `inv_decompositionCorestriction_localIdeleClassMap`: for every local class
  `a ∈ H²(Gal(E_w/F_v), E_wˣ)`, the global invariant of
  `decompositionCorestriction v w 2 (localIdeleClassMap v w 2 a)` is the local invariant
  `(I (residuePrime v)).relative (padicField v) (w.adicCompletion E) a`. Proof: choose places
  above every finite place of `F`, with `w` above `v`, and places above every infinite place.
  By `ideleLocalSection_comp_ideleQuotientCohomologyMap` the corestricted class is the
  idele-class image of `ideleLocalSection v w 2 a`. By agreement its invariant is the total
  idele invariant of this section, which is the local invariant of `a` by the Library's
  `totalIdeleInvariant_ideleLocalSection`.

The next three results take a number field `F'` in a tower `F → F' → E` and a surjective map
`Θ : H²(Gal(E/F'), C_E) ⟶ H²(Gal(E_w/F_v), C_E)` such that restriction to `Gal(E/F')`
followed by `Θ` is `decompositionRestriction v w 2` (hypothesis `hcomp`).

- `decompositionRestriction_surjective`: `decompositionRestriction v w 2` is surjective. It is
  the composite of `relativeIdeleClassRestriction_surjective` and `Θ`.
- `decompositionCorestriction_injective`: if moreover `[F' : F]` equals the index of
  `Gal(E_w/F_v)` (hypothesis `hdeg`), then `decompositionCorestriction v w 2` is injective.
  Proof: write a class in the kernel as `decompositionRestriction v w 2 b`. Then
  `[F' : F] • b = 0` because corestriction after restriction is multiplication by the index.
  By the restriction law, the invariant of the restriction of `b` to `F'` is
  `[F' : F] • inv F E b = 0`. So that restriction is zero by injectivity of `inv F' E`, and
  applying `Θ` shows that the class is zero.
- `localIdeleClassMap_eq_decompositionRestriction_iff_of_field`: under the same hypotheses,
  for every local class `a` and global class `b`,
  `localIdeleClassMap v w 2 a = decompositionRestriction v w 2 b` if and only if
  `[F' : F] • inv F E b` is the local invariant of `a`. Forward: apply `inv F E ∘ cor` to
  both sides, using `inv_decompositionCorestriction_localIdeleClassMap` on the left and
  cor ∘ res = index on the right. Backward: the corestrictions of both sides have the same
  invariant, so they are equal by injectivity of `inv F E`. Corestriction is injective, so the
  two sides are equal.

## The final theorem

`globalInvariantLocalFromTotalStatement` applies the last result with `F'` the decomposition
field `decompositionField v w` of [DecompositionField](DecompositionField.md) and with
`Θ = (decompositionCohomologyIso v w 2).hom`. It is surjective because it is an isomorphism.
The required inputs from that module are:

- `hcomp` is `relativeIdeleClassRestriction_comp_decompositionCohomologyIso v w 2`;
- `hdeg` follows from `finrank_decompositionField v w`, which gives `[F' : F]` as the index of
  the range of `decompositionHom v w`;
- `finrank_div_finrank_local v w` rewrites the natural-number quotient
  `Module.finrank F E / Module.finrank (padicField v).Carrier (w.adicCompletion E)` in the
  statement as `[F' : F]`. It uses the local Galois instance that the statement supplies.

The finiteness instance on `Gal(E/F) ⧸ range (decompositionHom v w)` needed by the
corestriction comes from `Fintype.ofFinite`.

## Exact statement interface

The complete, unapplied type of
`Langlands.ClassField.Global.globalInvariantLocalFromTotalStatement.{u}` is

```lean
Langlands.ClassField.Global.GlobalInvariantLocalFromTotalStatement.{u}
```

There are no parameters or hypotheses outside this closed proposition and no
specialization of its arbitrary common universe `u`. The exact-target proof
contribution by Worker 369 and Worker 226 reuses this declaration directly.

The proposition quantifies a local invariant family `I`, its `RelativeImages`
witnesses `hI`, and global invariant maps `inv`. From the global image law,
class-level restriction law, and agreement with the total idele invariant for
every choice of finite and infinite places, it concludes exactly
`FundamentalClass.InvariantLocalOnClasses I inv`. It proves neither existence
of the invariant families nor their total-agreement premise. No local conjugacy,
change-of-base naturality, local compatibility, transfer injectivity, or
surjectivity of idele-to-class H² is assumed as an additional premise.

## Provenance

The global argument is derived, not a verbatim theorem of a single source. It follows the
semilocal formalism of E. Artin and J. Tate, *Class Field Theory* (AMS Chelsea, 2009;
`artin-tate-2009-class-field-theory`). Preliminaries §1 (printed pp.1–2) treats the semilocal
Shapiro isomorphism with restriction and transfer. Chapter VII §3 (printed pp.42–48; PDF page =
printed page + 9) treats the total invariant and its agreement on quotient images. The
corestriction and the identity cor ∘ res = index are Milne, *Class Field Theory* (v4.03, 2020;
`milne-2020-class-field-theory`), Chapter II, Example 1.29 and Proposition 1.30 (printed p.70).
The surjectivity of restriction from the image and restriction laws, and the injectivity of
the corestriction obtained from it, are internal steps of this proof. They are proved only
under the stated hypotheses.
