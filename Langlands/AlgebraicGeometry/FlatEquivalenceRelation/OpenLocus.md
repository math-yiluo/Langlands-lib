# The open locus of the Hilbert scheme over which the classified family lies in an open

Authors: Worker 5705.

Helper module of the proof of
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement` (entry
module `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof`),
written for Task 5705 (`07219dde-fd87-48cf-83be-db16cbb3707c`) under operator request
`98389b48910e54088e0e2b2ba6aaad9c`. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.FlatEquivalenceRelation`, with the notation of
`FlatEquivalenceRelation.Classifier`. Here `C : Classifier f` and `f : X ⟶ S` is proper.

**The locus.**

- `Classifier.toX : D ⟶ X` is the universal closed subscheme mapped to `X`.
- `Classifier.locus U`, for an open `U ⊆ X`, is the open subscheme of `H` with underlying set
  the complement of `pD(toX⁻¹(X \ U))`. It is open because `pD` is proper, hence closed.
  `mem_locus`: `y ∈ locus U` exactly when every point of `D` over `y` maps into `U`.
- `Dl U` is `pD⁻¹(locus U)`, and `pDl U : Dl U ⟶ locus U` is the restriction of `pD`. It is
  flat, proper and locally of finite presentation (instances, by base change along an open
  immersion).
- `toU U : Dl U ⟶ U` is the factorization of `toX` through `U`. `isSeparated_toU`: it is
  separated when `πH` is.

**The classifying morphism over the locus.** Assume `hEq` and `hW` as in `Classifier`, with
`i : Z ⟶ X` a monomorphism.

- `graph_toX`: the graph `Z ⟶ D` followed by `toX` is `i`.
- `range_subset_locus`: **if `i` lands in `U`, then `φ` lands in `locus U`.** A point `d` of `D`
  over `φ z` comes from a point of `Z ×_H D` (Mathlib's
  `Scheme.Pullback.exists_preimage_pullback`). By `exists_factor` that point is
  `c ≫ t ≫ graph` for some `c` into `R`, so `toX d` lies in the range of `i`.
- `φl U hU : Z ⟶ locus U` and `graphl U hU : Z ⟶ Dl U` are the factorizations of `φ` and of the
  graph through the open subschemes, with `φl_ι`, `graphl_ι`, `graphl_pDl`, `graphl_toU`.
- `range_subset_coborderRange`: an immersion lands in Mathlib's `coborderRange`, the largest
  open subscheme in which its range is closed.
- `isClosedImmersion_graphl`: **for `U = i.coborderRange`, the graph `Z ⟶ Dl U` is a closed
  immersion**, when `πH` is separated and `i` is an immersion. The composite `graphl ≫ toU` is
  the closed immersion `i.liftCoborder : Z ⟶ U`, and `toU` is separated. Apply Mathlib's
  `IsClosedImmersion.of_comp`.

## Provenance

The open locus is an addition of this proof; it does not occur in Nitsure, *Construction of
Hilbert and Quot schemes*, Theorem 6.8 (pp.33–35). Nitsure uses the Hilbert scheme of the
quasi-projective scheme itself (his `X` is our `Z`). Its graph `(id, φ)` is a closed embedding
because the Hilbert scheme is separated (p.34). Here the Hilbert scheme is that of the projective
space `X = ℙⁿ_A` containing `Z`, since `HilbertSchemeUniversalFamilyStatement` needs a
projective family. The graph `Z ⟶ D` then has closed image only over the open locus of the
Hilbert scheme where the universal family lies in `i.coborderRange`.
