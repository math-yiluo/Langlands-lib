# Finite representatives of the full valuation lattice (Renard V.3.23, proof)

Author: Worker 114 (Task 5679, `cce59833-87fe-4fa2-bd38-c532167817a0`).
The product-section theorem it applies was written by Worker 1292.

`Langlands.Plancherel.RenardCartan.fullLatticeRepresentative` proves exactly
the published proposition
`Langlands.Plancherel.RenardCartan.FullLatticeRepresentativeStatement.{u}`
(module [`RenardLatticeComparisonStatement`](RenardLatticeComparisonStatement.md)),
at every universe `u`, with no added hypothesis. The statement's Lean/Markdown
pair and everything it imports are unchanged.

## Statement

For every nonarchimedean local field `F : Type u` (with the Library's field,
`ValuativeRel`, topology and `IsNonarchimedeanLocalField` instances, in either
characteristic), every actual connected reductive group scheme `Z` over
`Spec F`, every actual commutative group scheme `T` and every
`s : T.toGrp ⟶ Z` with `IsSplitComponent s`:

1. there is a set `F0` of points of `Z(F)` with `IsFiniteLatticeTransversal s F0`:
   `F0` is finite and `f ↦ latticeResidue s f` is a bijection from `F0` onto
   `Λ(Z)/splitValuationImage s`, where `Λ(Z) = rationalCharacterValuationImage Z`;
2. for every such `F0`, `tildeC0 s F0 = C0 T s * F0` is a valuation section
   (`IsValuationSection`: valuation is a bijection from it onto `Λ(Z)`), and
   the map `(c, f) ↦ rationalCharacterValuation Z (c * f)` on
   `C0 T s × F0` is injective.

## Implemented proof

The module contains three theorems.

- `latticeResidue_surjective s`: every residue class of
  `Λ(Z)/splitValuationImage s` is `latticeResidue s z` for some `z ∈ Z(F)`.
  A class is the image of some `y ∈ Λ(Z)` under the quotient map
  (`QuotientGroup.mk'_surjective`), and `y` is the valuation of some point
  (`MonoidHom.rangeRestrict_surjective`).
- `exists_isFiniteLatticeTransversal_of_finiteIndex s hfin`: if
  `splitValuationImage s` has finite index, let `σ` be the right inverse
  `Function.surjInv` of the surjective residue map and take `F0 = Set.range σ`.
  It is finite because the quotient is finite (Mathlib's instance
  `Subgroup.finite_quotient_of_finiteIndex` from `hfin`, then
  `Set.finite_range`). The residue map on `F0` is injective since
  `latticeResidue s (σ q) = q` (`Function.surjInv_eq`), and surjective since
  `σ q ∈ F0` has residue `q`.
- `fullLatticeRepresentative` introduces `F`, `Z`, `hZ`, `T`, `s`, `hs` and
  takes the two conjuncts of the published
  `splitComponentLattice F Z hZ T s hs` (Task 4160): finite index of
  `splitValuationImage s`, and `Set.BijOn` of the valuation from `C0 T s`
  onto `splitValuationImage s`.
  - The existence conjunct is `exists_isFiniteLatticeTransversal_of_finiteIndex`
    applied to the finite index.
  - For a given transversal `F0`, both the valuation-section property and the
    pair injectivity are exactly the conclusion of the published
    `isValuationSection_tildeC0_of_bijOn s hbij hF0`
    (module [`RenardDominantSections`](RenardDominantSections.md),
    Worker 1292), applied to the `BijOn` conjunct. That theorem proceeds as
    follows. Equal product valuations give equal quotient residues; points of
    `C0` have trivial residue because their valuations lie in the split image,
    so transversal injectivity identifies the `F0` factors; cancelling that
    factor and injectivity on `C0` identify the `C0` factors. For
    surjectivity, take the transversal point `f` in the residue class of a
    requested value `y`; the quotient of `y` by the valuation of `f` lies in the
    split image, and surjectivity onto it supplies `c ∈ C0` with
    valuation of `c * f` equal to `y`. Injectivity on the set of products then
    follows from injectivity on pairs through factorizations witnessing
    membership in `C0 T s * F0`.

The inspected axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the literature

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, V.3.23
(printed page 117 / PDF page 123): since the lattice `Λ(A)`, lifted to
the subgroup `C_A` in V.2.5, is a finite-index sublattice of `Λ(M)`, there is a finite set `F_M` of elements of `M` such
that `C_A F_M` is a set-theoretic lift of `Λ(M)` to `M`. The finite-index and
`C_A`-lift inputs are Renard V.2.5–V.2.6 (printed pp.107–108), provided in the
Library by `splitComponentLattice`. Renard leaves the choice of `F_M` and the
uniqueness of the factorization implicit; the Lean proof chooses
representatives with `Function.surjInv` and proves the pair injectivity
stated in the target. Renard's further choice of `F_M` inside the dominant set
`M^+` and the identity `C̃_A^+ = C_A^+ F_M` are not part of this target.

## Scope

This proves only `FullLatticeRepresentativeStatement`. It does not assert
that a transversal is chamber compatible or dominant, and does not prove
`SplitComponentKernelStatement` (proved in
[`SplitComponentKernelProof`](SplitComponentKernelProof.md)).
