# Mapping cocones of squares commuting up to homotopy (internal)

`Langlands/GaloisCohomology/CompactSupport/Internal/ConeHomotopy.lean`, namespace `Langlands.GaloisCohomology`. Internal: no stability promise.

A square `f ≫ β ≃ α ≫ f'` commuting up to a homotopy induces a map of mapping cocones
(`mappingCoconeNat.mapOfHomotopy`), compatible with the projections and the connecting maps, and an
isomorphism in homology when `α` and `β` are (`isIso_homologyMap_mapOfHomotopy`, by the five lemma).
Products on cones of cocycles, and the behaviour of the foundations' conjugation homotopy on cup
products of cochains (`conjHomotopyFun_cupCochain`), are used for the Mackey compatibility of cup
products.

```lean
noncomputable def mappingCoconeNat.mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f')) :
    mappingCoconeNat f ⟶ mappingCoconeNat f'
theorem mappingCoconeNat.isIso_homologyMap_mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f'))
    (hα : ∀ n, IsIso (homologyMap α n)) (hβ : ∀ n, IsIso (homologyMap β n)) (n : ℕ) :
    IsIso (homologyMap (mapOfHomotopy h) n)
```

## Outline of the proofs

The map `(x, c) ↦ (α x, β c + h x)` of cocones is a map of complexes by the homotopy
identity; it commutes with the projections and the connecting maps, and the five lemma applied to
the long exact sequences gives the isomorphism in homology. The lemmas on `seqProd` and
`conjHomotopyFun_cupCochain` compute the conjugation homotopy of the foundations on cup products of
cochains with a `0`-cochain.

## Declarations

`homotopyShiftF`, `mapOfHomotopyF`, `mapOfHomotopyF_comm`, `mapOfHomotopy`, `mapOfHomotopy_fst`, `inr_mapOfHomotopy`, `homologyδ_naturality_of_inr`, `isIso_homologyMap_of_comm`, `isIso_homologyMap_mapOfHomotopy`, `f_fst_eq_d_snd_of_d_eq_zero`, `f_fst_eq_zero_of_d_eq_zero`, `homotopy_apply_zero_of_d_eq_zero`, `homotopy_apply_succ_of_d_eq_zero`, `snd_sub_eq_neg_d`, `_root_.Langlands.GaloisCohomology.homologyπ_eq_of_iCycles_sub_eq_d`, `homologyMap_mapOfHomotopy_coconeLeft`, `seqProd`, `seqProd_succ`, `partialProd_seqTuple`, `seqProd_prismSeq_of_ge`, `seqProd_prismSeq_of_le`, `cupCochain_seqTuple`, `cupCochain_seqTuple_prismSeq_of_le`, `cupCochain_seqTuple_prismSeq_add`, `conjHomotopyFun_cupCochain`, `conjHomotopyFun_cupCochain_zero_left`, `conjHomotopyFun_cupCochain_zero_right`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/MackeyFormula/ConeHomotopy.lean`, `PoincarePairs/ConeProduct.lean` and `PoincarePairs/ConjHomotopyFunCupCochainZeroRight.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's; the three files are merged into one file named for its content.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
