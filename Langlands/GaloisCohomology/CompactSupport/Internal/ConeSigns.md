# Leibniz pairings on mapping cocones and their signs (internal)

`Langlands/GaloisCohomology/CompactSupport/Internal/ConeSigns.lean`, namespace
`Langlands.GaloisCohomology`. Internal: no stability promise.

Let `f : K ⟶ L` and `g : Q ⟶ P'` be morphisms of `ℕ`-indexed complexes and `ρ : N ⟶ N'`. Given
Leibniz pairings `K × N → Q` and `L × N' → P'` with `g(x·y) = f(x)·ρ(y)`, the pairing
`(x, c)·y = (x·y, c·ρ(y))` is a Leibniz pairing `Cocone(f) × N → Cocone(g)`
(`LeibnizPairing.coconeLeft`); with the cocone in the right factor the shifted component carries
the sign `(−1)ʳ` (`coconeRight`).

```lean
noncomputable def LeibnizPairing.coconeLeft (μL : LeibnizPairing L N' P') (ρ : N ⟶ N')
    (μK : LeibnizPairing K N Q) (hc : …) : LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat g)
theorem LeibnizPairing.coconeLeft_homology_homologyδ … :
    (coconeLeft μL ρ μK hc).homology h' ((mappingCoconeNat.homologyδ f r).hom c) z =
      (mappingCoconeNat.homologyδ g n).hom (μL.homology h c ((HomologicalComplex.homologyMap ρ s).hom z))
theorem LeibnizPairing.coconeLeft_homology_eq_coconeRight_homology … :
    (coconeLeft …).homology h x (H(fst) y) = (coconeRight …).homology h (H(fst) x) y
```

## Outline of the proofs

The Leibniz rule for the cone pairings is checked on pairs, using the shift conventions of
`Internal/MappingCocone.lean` (`shiftLeft_leibniz`, `shiftRight_leibniz`). On the image of the
connecting map, a class `δ[c]` is represented by `(0, c)` (`exists_homologyδ_homologyπ`), and the
product `(0, c)·y = (0, c·ρ(y))` represents `δ[c·ρ(y)]`. For the comparison of the two pairings,
the difference of the left and right products of two cycles of cocones is the boundary of an
explicit element built from `shiftBoth` (`coconeLeftμ_sub_coconeRightμ_eq_d`), so they agree in
homology.

## Declarations

In namespace `LeibnizPairing`: `shiftLeft`, `shiftLeft_succ`, `shiftLeft_leibniz`, `coconeLeftμ`,
`coconeLeftμ_apply`, `coconeLeft`, `coconeLeft_homology_homologyδ`, `shiftRight`,
`shiftRight_succ`, `shiftRight_leibniz`, `coconeRightμ`, `coconeRightμ_apply`, `coconeRight`,
`shiftBoth`, `shiftLeft_sub_shiftRight`, `coconeLeftμ_sub_coconeRightμ_eq_d`,
`coconeLeft_homology_eq_coconeRight_homology`; `mappingCoconeNat.exists_homologyδ_homologyπ`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/CompactSupportCohomology/ConePairing.lean` and
`CompactSupportCohomology/ConeSymmetry.lean`. The repository has no licence file; its text is used with
attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's; the two files are
merged into one file named for its content.

## References

The construction is not in the literature in this form; it is the cochain-level form of the cup
product on cohomology with compact support of J. S. Milne, *Arithmetic Duality Theorems*, 2nd
edition (BookSurge 2006), chapter II, §2 (pp. 165–166, the mapping cone definition).
