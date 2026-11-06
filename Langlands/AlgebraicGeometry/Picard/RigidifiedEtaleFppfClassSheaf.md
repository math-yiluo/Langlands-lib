# The etale Picard class sheaf satisfies fppf descent when a rigidification exists

Module `Langlands.AlgebraicGeometry.Picard.RigidifiedEtaleFppfClassSheaf`.

## Setting

Throughout, `f : X ⟶ S` is a morphism of schemes in universe `u`. The
other data are a section `ε : S ⟶ X` with `section_eq : ε ≫ f = 𝟙 S` and the
*universal structure-sheaf condition*

```
hO : ∀ (T : Over S) (U : T.left.Opens),
  IsIso (((relativeProjection f).app T).app U)
```

This condition says that for every test scheme `T` over `S`, the map
`O_T → (p_T)_* O_{X_T}` is an isomorphism on every open of `T`, where
`p_T : X ×_S T → T` is the base change of `f` (Library
`relativeProjection f`). No quasi-compactness, quasi-separatedness, flatness or
properness of `f` is assumed.

The objects compared are all on the full slice `Over S`, with values in
`Type (u+1)`:

* `RigidifiedLineBundle.classPresheaf pullbackCoherence f ε section_eq`: the
  presheaf of isomorphism classes of line bundles on `X ×_S T` rigidified along
  the base-changed section;
* `RelativePicard.classPresheaf f`: the presheaf of isomorphism classes of
  ordinary line bundles on `X ×_S T`;
* `RelativePicard.etaleClassSheafPresheaf f`: the underlying presheaf of the
  actual etale sheafification `RelativePicard.etaleClassSheaf f` of that
  presheaf, with the unit `RelativePicard.toEtaleClassSheaf f`
  (module `Picard/EtaleFppfSheafComparison`);
* `RigidifiedLineBundle.forgetClassNatTrans f ε section_eq`: the published
  natural transformation that forgets the rigidification.

## Declarations

* `classPresheaf_isSheaf_fppf f ε section_eq hO` states that the rigidified
  class presheaf is a sheaf for `Scheme.fppfTopology.over S`.
* `forgetClassNatTrans_isLocallySurjective_etale f ε section_eq` states that
  forgetting the rigidification is locally surjective for
  `Scheme.etaleTopology.over S`.
* `forgetClassNatTrans_isLocallyInjective_etale f ε section_eq` states that it
  is locally injective for the same topology.
* `forgetClassNatTrans_toEtaleClassSheaf_isIso f ε section_eq hP` assumes that
  the rigidified class presheaf is an etale sheaf (`hP`). It concludes that
  `forgetClassNatTrans f ε section_eq ≫ RelativePicard.toEtaleClassSheaf f` is
  an isomorphism of presheaves on `Over S`.
* `rigidifiedEtaleClassIso f ε section_eq hO` is the definition named by this
  record: under `hO`, a natural isomorphism of presheaves on `Over S`

  ```
  classPresheaf pullbackCoherence f ε section_eq ≅
    RelativePicard.etaleClassSheafPresheaf f
  ```

  whose forward map is `forgetClassNatTrans f ε section_eq ≫
  RelativePicard.toEtaleClassSheaf f` (lemma `rigidifiedEtaleClassIso_hom`,
  proved by `rfl`). In words: rigidified line-bundle classes on `X ×_S T` are
  the same as sections over `T` of the etale sheafification of ordinary
  line-bundle classes.
* `etaleClassSheafPresheaf_isSheaf_fppf f ε section_eq hO` is the main result:
  `Presheaf.IsSheaf (Scheme.fppfTopology.over S)
  (RelativePicard.etaleClassSheafPresheaf f)`. It says that the actual etale
  sheafification of ordinary line-bundle classes already satisfies fppf
  descent.

## Proof

1. *Rigidified classes form an fppf sheaf.* By the published
   `relative_iso_subsingleton`, `hO` makes every isomorphism set between two
   rigidified bundles on `X ×_S T` subsingleton. The published criterion
   `OverFppfSheaf.isSheaf_fppfTopology_over` reduces the fppf sheaf condition
   to two inputs. The first is the Zariski sheaf condition, from
   `classPresheaf_isSheaf_zariski_of_unique`. The second is the singleton
   condition along `Spec.map φ : Spec R' → Spec R` for every ring map
   `φ : R → R'` such that `Spec.map φ` is flat and surjective (equivalently,
   `φ` is faithfully flat), from `classPresheaf_isSheafFor_affine`. That
   lemma uses the published descent theorems
   `LineBundleIsoDescent.lineBundleIsoDescent` and
   `lineBundleDescentEffective`. This argument is the one in the published
   proof of `rigidifiedFppfComparison`. That proof does not export the sheaf
   property as a separate lemma, so this module states it.
2. *Local surjectivity.* The published
   `forgetClassNatTrans_isLocallySurjective_zariski` gives Zariski-local
   surjectivity of the forgetful map. Every Zariski covering sieve on the slice
   is an etale covering sieve (Mathlib's `Scheme.zariskiTopology_le_etaleTopology`),
   so `Presheaf.isLocallySurjective_of_le` transfers it to the etale topology.
3. *Local injectivity.* The forgetful map is injective on every object by the
   published `forgetClasses_injective`, hence locally injective for every
   topology.
4. *Comparison with the etale sheafification.* Assume the rigidified class
   presheaf is an etale sheaf. The composite with the sheafification unit is
   a morphism of etale sheaves. It is locally injective and locally surjective,
   because composing with the unit of sheafification preserves both properties.
   By Mathlib's `Sheaf.isLocallyBijective_iff_isIso` it is an isomorphism. This
   follows the published `toClassPicardSheaf_isIso_of_isSheaf`, with the fppf
   topology replaced by the etale one.
5. *The isomorphism.* The fppf topology on `Over S` is finer than the etale
   one (`Sites.etaleTopologyOver_le_fppfTopologyOver`), so step 1 also gives
   the etale sheaf condition. Step 4 then makes the composite an isomorphism,
   and `rigidifiedEtaleClassIso` is that isomorphism (`asIso`).
6. *Main theorem.* The rigidified class presheaf is an fppf sheaf (step 1),
   and `rigidifiedEtaleClassIso` identifies it with
   `RelativePicard.etaleClassSheafPresheaf f`, so the latter is an fppf sheaf
   too (`Presheaf.isSheaf_of_iso_iff`).

## Use and provenance

This is an internal interface for the corrected Artin route to Picard
algebraicity. That route follows Artin, *Versal deformations and algebraic
stacks* (1974), Appendix item 2, printed pp.186-187, which uses the etale
sheaf of isomorphism classes. The interface supplies the hypothesis
`Presheaf.IsSheaf (Scheme.fppfTopology.over S) (RelativePicard.etaleClassSheafPresheaf f)`
of `RelativePicard.classSheaf_algebraicSpace_of_etale_atlas`
(`Picard/EtaleFppfAtlasTransport`), for any `f` with a section and the
universal structure-sheaf condition. Mathematically it is the standard
argument behind Faltings–Chai, *Degeneration of Abelian Varieties*, Chapter I,
Definition 1.4(b), printed p.2 (PDF p.14): along the unit section, the relative
Picard functor is canonically isomorphic to the functor of rigidified classes.
That source is cited only as motivation; the Lean proof above is
self-contained over the cited Library and Mathlib results. Abelian schemes are the
intended application: their unit section gives `ε`, and `hO` comes from the
published global-functions theorem for smooth proper morphisms with
geometrically connected fibres. That application is not part of this module.
