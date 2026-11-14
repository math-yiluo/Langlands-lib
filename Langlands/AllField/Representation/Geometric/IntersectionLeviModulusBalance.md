# All-field port of `Langlands.Representation.Geometric.IntersectionLeviModulusBalance`

`Langlands.AllField.Representation.Geometric.IntersectionLeviModulusBalance` is the all-field port of the Library module `Langlands.Representation.Geometric.IntersectionLeviModulusBalance`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Geometric.IntersectionLeviModulusBalance` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The block-normalization balance of the explicit moduli on the intersection Levi.

## Proof route

The original proof applies `Langlands.Geometric.intersectionLeviDiagonalCharacterTheorem`, which assumes `CharZero F` (obtained there from the `ℚ_[p]`-algebra structure of the p-adic field). The port applies instead `Langlands.AllField.Geometric.intersectionLeviDiagonalCharacter` (module `Langlands.AllField.Representation.Geometric.IntersectionLeviDiagonalCharacter`), which needs only an element of `F` other than `0` and `1`, supplied by `Langlands.AllField.Geometric.exists_ne_zero_ne_one`. Statements are unchanged.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.MinimalWeylTransportProof`
- `Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountProof`
- `Langlands.AllField.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof`
- `Langlands.AllField.Representation.Geometric.IntersectionLeviDiagonalCharacter`

## Declarations

- `Langlands.AllField.Geometric.leviModulus_of_diagonal` (theorem): The explicit block modulus of a diagonal element is the product of its
  root quotients over pairs of coordinates in increasing blocks.
- `Langlands.AllField.Geometric.refinedLeviModulus_of_diagonal` (theorem): The explicit refined modulus of a diagonal element, when the inner blocks
  compare as a function `g` of the standard coordinates.
- `Langlands.AllField.Geometric.intersectionLeviModulusBalance` (theorem): The block-normalization balance on the actual intersection Levi
  `M ∩ w⁻¹ N w`. For `m` there, with `m'` its conjugate in `N ∩ w M w⁻¹`, the
  explicit moduli of `B`, of `C` and of the two Levi-intersection refinements
  satisfy `δ_B(m) δ_C(m') δ_{B,S}(m) = δ_{C,R}(m') ε(m')²`, where `ε` is the actual
  Haar modulus of `V ∩ w P w⁻¹`. Each modulus is evaluated at any coordinate
  element with the same underlying matrix.
- `Langlands.AllField.Geometric.intersectionLeviModulusBalance_sourceLevi` (theorem): The same balance in the source-Levi coordinates: `m` in `M ∩ w⁻¹ N w` as a
  subgroup of the product Levi of `B`, `m'` its conjugate in the product Levi of
  `C`, the refined moduli evaluated through the Levi parts of the intersection
  equalities, and the Haar modulus evaluated at the element of `N ∩ w M w⁻¹`
  with the matrix of `m'`.
- `Langlands.AllField.Geometric.intersectionLeviHalfModulusBalance_sourceLevi` (theorem): The positive complex halves of the source-Levi balance: the three source and
  target half moduli equal the refined target half modulus times the complex Haar
  modulus of `V ∩ w P w⁻¹`.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.prod_pairs_reindex_iff`, `Langlands.Geometric.modulus_balance_root_products`, `Langlands.Geometric.prod_within_blocks`, `Langlands.Geometric.levi_block_diagonal`, `Langlands.Geometric.refinement_lt_iff_of_sourceLevi`, `Langlands.Geometric.intersectionLeviNormalizationRatio`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
