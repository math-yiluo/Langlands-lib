# Čech cochains of a Galois covering and injective sheaves

Worker 749. This module is a derived categorical helper for the planned proof of
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`. Its main theorem is
`isZero_groupCohomology_rep_of_injective`. It says that for a Galois covering
`G : GaloisCovering J Γ V' V` (module `Langlands.Cohomology.GaloisCovering`) and an injective
sheaf `I` of `R`-modules, `groupCohomology (G.rep I) (n + 1)` is zero for every `n`. This is
the `injective_acyclic` hypothesis of a Galois–Čech system
(`Langlands.Cohomology.GaloisCartan`) at a single covering.

## Background and provenance

Milne, *Étale Cohomology* (1980), III Lemma 2.4, printed p. 98, shows that Čech cohomology of
an injective presheaf vanishes in positive degrees. Milne III Example 2.6, printed pp. 99–100,
identifies the Čech complex of a finite Galois covering with the inhomogeneous cochain
complex of its group. Both are in source `milne-1980-etale-cohomology`. This module combines
the two arguments for the elementwise Galois coverings of `GaloisCovering`, with no fibre
products or coproducts in the site category.

The proof is internal. The exactness input is the Library's free Čech nerve theorem
`quasiIso_freeCechAugmentation_of_locally_surjective` (`Langlands.Cohomology.SiteCech`). The
identification with group cochains is proved through elements, using local transitivity and
local freeness. Throughout, `C` is locally `w`-small, `R` and `Γ` lie in `Type w`, and module
sheafification exists.

## Exactness transfer

`exactAt_of_comparison` is a general lemma on cochain complexes of modules, possibly in
different universes. Let additive maps `e k : K.X k → L.X k` commute with the differentials,
with `e (n + 1)` surjective and `e (n + 2)` injective. Then exactness of `K` at `n + 1`
implies exactness of `L` at `n + 1`.

## Tuples and Čech terms

- `presheafArrow G` is the arrow `shrinkYoneda.map G.p` of presheaves of types.
  `cechTerm G n` is the degree-`n` term of its Čech nerve.
  `isLocallySurjective_presheafArrow` derives local surjectivity of the arrow from
  `G.covering`.
- A tuple `t : Fin (n + 1) → (U ⟶ V')` with a common composite to `V` gives
  `tupleHom t : shrinkYoneda U ⟶ cechTerm n`, built with `WidePullback.lift`.
  Supporting lemmas: `tupleHom_π`, `tupleHom_ext`, `map_comp_tupleHom`.
  `tupleHom_δ`: the face `δ j` deletes entry `j.succAbove`.
- `tupleOf x` recovers the tuple of an element `x` of a Čech term, through full faithfulness
  of `shrinkYoneda`. The lemmas `tupleOf_comp_p`, `tupleHom_tupleOf`,
  `tupleOf_shrinkYonedaEquiv_tupleHom` and `tupleOf_map` show that elements correspond to
  tuples, naturally in `U`.

## Values of Čech cochains

- `valueHom t φ` is the value of a Čech cochain `φ : freeSheaf(cechTerm n) ⟶ I` on a tuple
  `t`. It is `freeRepresentableHomEquiv` of the composite with `tupleHom t`, and it is linear
  in `φ`.
- `valueHom_comp`: values are natural in the source of the tuple.
- `valueHom_δ_comp`: precomposition with a face gives the value on the shortened tuple.
- `valueHom_eq_homEquiv`: values are computed through the free-sheaf adjunction.
- `cochain_ext`: a cochain is determined by its values on all tuples.
- `cechChain` is the free sheaf Čech chain complex, and `cechCochain G R I` is its linear Hom
  complex into `I`. The lemmas `cechCochain_d_apply`, `cechChain_d` and `valueHom_cech_d`
  express the differential on values as an alternating sum over deleted entries.
- `cechCochain_exactAt_of_injective`: for injective `I`, `cechCochain` is exact in positive
  degrees. This uses local surjectivity, the Library's quasi-isomorphism theorem and
  `exactAt_linearYonedaObj_of_injective`.

## Comparison with inhomogeneous cochains

- `hpat g k := G.deck (Fin.partialProd g k)⁻¹` is the homogeneous tuple of deck
  transformations of `g : Fin n → Γ`. It satisfies `hpat_comp_p` and `hpat_zero`.
- `compare G R I n` is the linear map from Čech cochains to `(Fin n → Γ) → I(V')`, given by
  `φ ↦ (g ↦ valueHom (hpat g) φ)`.
- `compare_d`: `compare` commutes with Mathlib's differential on
  `groupCohomology.inhomogeneousCochains (G.rep I)`. Here `γ` acts by restriction along
  `deck γ⁻¹`.
  - The face deleting entry `0` gives the term `ρ(g 0)`, by `Fin.partialProd_succ'` and
    `deck_mul`.
  - The face deleting entry `j + 1` gives the `Fin.contractNth j` term, by
    `Fin.partialProd_contractNth`.
- `patternSieve t` is the sieve of arrows `k` with `k ≫ t = (k ≫ t 0) ≫ hpat g` for some `g`.
  `patternSieve_mem` shows that it covers. It contains a finite intersection of the sieves
  from `locally_transitive` (`finInter`, `finInter_mem`). The tuple `g` is recovered from the
  deck elements by `Fin.partialProd_left_inv`.
- `compare_injective`: on the pattern sieve, every value is a restriction of a value of the
  form `compare φ g`. Then `eq_of_sieve` and `cochain_ext` give injectivity.
- `map_eq_of_hpat_eq`: two homogeneous deck tuples through the same arrow `f` give the same
  restriction of any family of values. If the empty sieve covers the source of `f`, sections
  over it are equal. Otherwise `locally_free` forces the partial products to agree, and then
  so do the tuples (`eq_of_partialProd_eq`). The helper `pattern_comp` restricts a pattern
  along an arrow.
- `glue c t` glues the local values `I.map (k ≫ t 0) (c g)` along the pattern sieve, using
  `Presheaf.IsSheaf.amalgamate`. `glue_spec` characterizes it through any pattern witness.
  `glueHom c`, with `glueHom_app` and `glue_congr`, assembles these into a natural
  transformation from the Čech term to the underlying presheaf of `I`.
- `compare_surjective`: the adjoint of `glueHom c` is a Čech cochain whose comparison is `c`.
- `isZero_groupCohomology_of_compare` transfers exactness along `compare`.
  `isZero_groupCohomology_rep_of_injective` is the unconditional result.

## Scope

All statements are categorical. Nothing analytic is asserted. Checking the fields of
`GaloisCovering` for analytic Galois coverings, and passing to filtered colimits over
neighbourhoods, are separate obligations.
