# Localization homomorphisms of `G_S`

`Langlands/Galois/RestrictedRamification/Localization.lean`, namespace `Langlands.Galois`.

Let `K : Type u` be a number field, `Ω : Type v` a Galois extension of `K`, `S` a set of finite
places and `ι : PlaceEmbeddings K Ω`.

**Localization homomorphisms.** `localizationHom ι S v : G_{K_v} →ₜ* G_S` is the decomposition
homomorphism of `ι.finite v` restricted to `K_S`, at every finite place `v` (for `v ∉ S` it factors
through the unramified quotient; that is not proved here), and `realLocalizationHom ι S w` the same
at an infinite place `w`. Here `G_{K_v} = Gal(AlgebraicClosure K_v / K_v)`, which is Mathlib's
`Field.absoluteGaloisGroup K_v` by definition. They are compatible with `G_S → G_T`; another choice
`ι'` changes each of them by conjugation by an element of `G_S`; for `PlaceEmbeddings.standard K`
they are Mathlib's `Field.absoluteGaloisGroup.map (algebraMap K K_v)` followed by restriction.

```lean
def localizationHom (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →ₜ* GaloisGroupUnramifiedOutside K Ω S
def realLocalizationHom (ι : PlaceEmbeddings K Ω) (S) (w : InfinitePlace K) :
    Gal(AlgebraicClosure w.Completion/w.Completion) →ₜ* GaloisGroupUnramifiedOutside K Ω S
theorem localizationHom_apply (v) (σ) (x : maximalUnramifiedOutside K Ω S) :
    ι.finite v ((localizationHom ι S v σ x : maximalUnramifiedOutside K Ω S) : Ω) = σ (ι.finite v x)
theorem localizationHom_standard (S) (v) (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    localizationHom (PlaceEmbeddings.standard K) S v σ =
      AlgEquiv.restrictNormalHom (maximalUnramifiedOutside K (AlgebraicClosure K) S)
        (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) σ)
theorem exists_localizationHom_eq_conj (ι ι' : PlaceEmbeddings K Ω) (v) :
    ∃ g : GaloisGroupUnramifiedOutside K Ω S, ∀ σ, localizationHom ι' S v σ = g⁻¹ * localizationHom ι S v σ * g
```

**The place of an embedding.** For number fields `F → L`, a finite place `v` of `F` and
`j : L →ₐ[F] K̄_v` (`K̄_v = AlgebraicClosure F_v`): through `F_v ⊗_F L ≅ ∏_{w | v} L_w`
(`completionsTensorEquiv`, the Library's `finiteTensorMap`, bijective by
`completedTensorComparison`), `j` extends to an `F_v`-algebra map `∏ L_w → K̄_v`, which is nonzero
on exactly one factor: this is the place `placeOfAlgHom j` of `L` above `v`, and `j` extends to
`completionEmbeddingOfAlgHom j : L_w →ₐ[F_v] K̄_v`. Every place above `v` arises; two embeddings
have the same place if and only if they differ by an element of `Gal(K̄_v / F_v)`; the subgroup of
`Gal(K̄_v / F_v)` fixing `j(L)` is `Gal(L̄_w / L_w)` (`fixingOfAlgHomEquiv`).

**Localization of an open subgroup** (Mackey places). Let `L` be a number field in `K_S` with
`K → L → Ω`, `U = fixingOpenSubgroup S hL` and `K, L, Ω : Type u`. For `v ∈ S` and `x ∈ G_S`, the
foundations' Mackey subgroup `mackeySubgroup U (localizationHom ι S v) x` (the `σ ∈ G_{K_v}` with
`x σ x⁻¹ ∈ U`) is the subgroup fixing the embedding `localEmbedding hL ι v x = ι_v ∘ x⁻¹|_L`; the
double cosets correspond to the places of `L` above `S`, and each Mackey subgroup is `G_{L_w}`,
compatibly with `U ≅ G_{S_L}(L)` and the localization of `G_{S_L}(L)` at `w`:

```lean
def mackeyPlaceEquiv (S) (hL) (ι) :
    (Σ v : S, MackeyDoubleCoset (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom) ≃ finitePlacesAbove L S
def mackeyLocalEquiv (v) (x : GaloisGroupUnramifiedOutside K Ω S) :
    mackeySubgroup (fixingOpenSubgroup S hL : Subgroup _) (localizationHom ι S v).toMonoidHom x ≃ₜ*
      Gal(AlgebraicClosure ((localPlace hL ι v x).1.adicCompletion L)/(localPlace hL ι v x).1.adicCompletion L)
theorem exists_fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom [IsGalois L Ω]
    (ιL : PlaceEmbeddings L Ω) (v) (x) :
    ∃ g : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S), ∀ σ,
      fixingOpenSubgroupEquiv S hL (mackeyConj (fixingOpenSubgroup S hL : Subgroup _)
          (localizationHom ι S v).toMonoidHom x σ) =
        g⁻¹ * localizationHom ιL (finitePlacesAbove L S) (localPlace hL ι v x).1 (mackeyLocalEquiv hL ι v x σ) * g
```

## Outline of the proofs

- `localizationHom_eq_quotientMap`: restricting the decomposition homomorphism of `ι_v` to `K_S`
  is the decomposition homomorphism of `ι_v|_{K_S}` (`decompositionHom_comp_val`); with
  `restrict_quotientMap` this gives `restrict_localizationHom`, and with
  `PlaceEmbeddings.decompositionHom_standard_finite` the comparison with Mathlib.
- Conjugation: two embeddings of `K_S` differ by an automorphism (`exists_eq_comp_of_normal`).
- Places: a ring homomorphism from a finite product of rings to a field sends exactly one
  idempotent `e_w` to `1` (`exists_unique_map_single_one_eq_one`) and factors through that
  coordinate. An embedding `c : L_w → K̄_v` extending `j` gives the factorization through
  coordinate `w`, hence `w = placeOfAlgHom j` (`eq_placeOfAlgHom`); every `w` arises from
  `IsAlgClosed.lift` on `L_w`. Two embeddings with the same place give two embeddings of `L_w`,
  which differ by an automorphism of `K̄_v` over `F_v` (extend the isomorphism of their images).
- `K̄_v` is algebraic over `L_w` through `completionEmbeddingOfAlgHom j`, hence an algebraic
  closure of it (`closureEquivOfAlgHom`); elements of `Gal(K̄_v / F_v)` fixing `j(L)` fix
  `j(L_w)` (agreement on the dense image of `L`: `adicCompletion_algHom_ext`) and correspond to
  `Gal(L̄_w / L_w)`; continuity of the inverse as above, and compactness gives a homeomorphism.
- Mackey places: `σ ∈ H_x` iff `x σ x⁻¹` fixes `L` iff `σ` fixes `localEmbedding x`
  (`mem_mackeySubgroup_iff`); changing `x` within its double coset changes the embedding by an
  element of `G_{K_v}` (`localEmbedding_mul`) and so not the place. Injectivity: equal places give
  embeddings conjugate under `G_{K_v}`, hence equal double cosets; surjectivity: every embedding of
  `L` is `localEmbedding x` for some `x` (`exists_localEmbedding_eq`).
- Compatibility: `fixingOpenSubgroupEquiv_mackeyConj` is checked on elements with
  `decompositionHom_eq_iff`, using the extension `lift x` of `x` to `Ω`; any other embedding of
  `K_{S_L}` differs by conjugation.

## Declarations

- Localization: `localizationHom`, `realLocalizationHom`, `localizationHom_apply`,
  `realLocalizationHom_apply`, `localizationHom_eq_quotientMap`,
  `realLocalizationHom_eq_quotientMap`, `restrict_localizationHom`, `restrict_realLocalizationHom`,
  `exists_localizationHom_eq_conj`, `exists_realLocalizationHom_eq_conj`,
  `localizationHom_standard`, `realLocalizationHom_standard`.
- Places of an embedding: `exists_unique_map_single_one_eq_one`,
  `map_eq_map_single_of_map_single_one`, `completionsTensorEquiv`, `completionsTensorEquiv_tmul`,
  `completionsTensorEquiv_one_tmul`, `tensorLiftOfAlgHom`, `tensorLiftOfAlgHom_completionsTensorEquiv`,
  `tensorLiftOfAlgHom_completionsTensorEquiv_tmul`, `tensorLiftOfAlgHom_algebraMap`,
  `exists_unique_tensorLiftOfAlgHom_single`, `placeOfAlgHom`, `tensorLiftOfAlgHom_single_placeOfAlgHom`,
  `eq_placeOfAlgHom_of_tensorLiftOfAlgHom`, `pi_single_algebraMap`, `completionEmbeddingOfAlgHom`,
  `tensorLiftOfAlgHom_eq`, `completionEmbeddingOfAlgHom_algebraMap`, `adicCompletion_algHom_ext`,
  `eq_placeOfAlgHom`, `exists_placeOfAlgHom_eq`, `placeOfAlgHom_comp`, `exists_algEquiv_comp_eq`,
  `exists_algEquiv_of_placeOfAlgHom_eq`, `apply_completionEmbeddingOfAlgHom_of_forall`.
- Fixing groups: `charZero_adicCompletion` (a local instance in this file), `closureEquivOfAlgHom`,
  `closureEquivOfAlgHom_completionEmbedding`, `closureEquivOfAlgHom_symm_algebraMap`,
  `fixingOfAlgHom`, `mem_fixingOfAlgHom_iff`, `fixingOfAlgHomToAut`, `autToFixingOfAlgHom`,
  `fixingOfAlgHomMulEquiv`, `fixingOfAlgHomMulEquiv_apply`,
  `continuous_coe_fixingOfAlgHomMulEquiv_symm`, `fixingOfAlgHomEquiv`, `fixingOfAlgHomEquiv_apply`;
  `continuousMulEquivOfSubgroupEq`.
- Mackey places: `localEmbedding`, `localEmbedding_apply`, `mem_mackeySubgroup_iff`,
  `mackeySubgroup_eq`, `localEmbedding_mul`, `exists_localEmbedding_eq`, `localPlace`,
  `localPlace_mul`, `mackeyPlace`, `mackeyPlace_injective`, `mackeyPlace_surjective`,
  `mackeyPlaceEquiv`, `coe_mackeyPlaceEquiv`, `localEmbeddingOver`, `localEmbeddingOver_apply`,
  `mackeyLocalEquiv`, `mackeyLocalEquiv_apply`, `fixingOpenSubgroupEquiv_mackeyConj`,
  `exists_fixingOpenSubgroupEquiv_mackeyConj_eq`,
  `exists_fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files under
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`: `LocalMaps.lean` (section `Places`,
lines 181–201: `decompHomS`), `BaseChangePlaces.lean`, `BaseChangeMackey.lean` (`gsAutLift` is
`GaloisGroupUnramifiedOutside.lift` of `MaximalExtension.lean`), `BaseChange.lean`; lines 19–55 of
`GlobalClassFormation/LocalLimits/IsScalarTowerFiniteSubfieldAlgebraicClosure.lean` (the two lemmas
on idempotents). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: `decompHomS` and
`gsFinFamily` are `localizationHom` for a `PlaceEmbeddings`; the real places
(`RealPlaces/GSDefs.lean:22`) are `realLocalizationHom` at every infinite place; the source's
semi-local algebras (`GroundTheory.Global.SemiLocal.tensorEquiv`, `PlacesOver`, `CompletionsOver`)
are replaced by the Library's `Langlands.Global.AdelicFunctoriality.finiteTensorMap`,
`FinitePlacesAbove` and `completedTensorComparison`; the family of an open subgroup and its index
(`MackeyIndex`, `mackeyGroup`, `mackeyFamily` of `MackeyFormula/CompactSupport.lean`) are written
with the foundations' `MackeyDoubleCoset`, `mackeySubgroup`, `mackeyConj`; names
`gsLocalEmbedding` → `localEmbedding`, `gsLocalPlace` → `localPlace`, `gsLocalEmbeddingOver` →
`localEmbeddingOver`, `gsMackeyLocalEquiv` → `mackeyLocalEquiv`, `gsBaseChange_mackeyConj` →
`fixingOpenSubgroupEquiv_mackeyConj`, `exists_gsBaseChange_mackeyFamily_eq` →
`exists_fixingOpenSubgroupEquiv_mackeyConj_eq`; `localizationHom_standard`, the comparison of two
choices and the version with `PlaceEmbeddings L Ω` are new.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VIII, §1, p. 427 (fixed embeddings `i_p : k̄ → k̄_p` and the
  local Galois groups `G(K_p | k_p)` as decomposition groups), and chapter VIII, §6,
  Definition (8.6.2), p. 481 (the localization maps).
- J. Neukirch, *Algebraic Number Theory* (translated by N. Schappacher, Springer 1999), chapter II,
  §8: Extension Theorem (8.1), pp. 161–162 (places of `L` above `v` and embeddings `L → K̄_v` up to
  conjugation over `K_v`), Proposition (8.3), p. 164 (`L ⊗_K K_v ≅ ∏_{w | v} L_w`).
