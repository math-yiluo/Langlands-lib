# Actual relative root ranks and rational character restriction

Author: Worker 1230.

This internal interface measures ranks on the existing group-scheme lattices. For an arbitrary field `k : Type u`, `splitTorusRank T` is the rational dimension of the full lattice `characterLattice T`, namely `finrank ℚ (ℚ ⊗[ℤ] characterLattice T)`. Its geometric interpretation as a split rank is intended when `T` is a split torus. `splitTorusRank_splitTorus` proves that for the actual split torus indexed by any finite type `I` it equals `Nat.card I`. The proof uses the published lattice equivalence, `RationalSpan.tensorEquivPi`, and the dimension of a finite function space. Empty `I` is allowed.

`rationalCharacterRank G` similarly measures the rationalized module of actual homomorphisms `G → 𝔾_m`. `rationalCharacterRestrictRat f` is Mathlib scalar extension of the published `characterRestrict f`; it sends `q ⊗ χ` to `q ⊗ (χ ∘ f)`. Its pure-tensor and `toRat` computation rules are definitional equalities. These definitions require no reductivity or finiteness assumption; the structural statements must supply finiteness when using these natural-number ranks.

For affine `G`, `relativeRootRank i` is the rational dimension of the published `relativeRootSpan i`. `simpleRelativeRootVector i ν` inserts each actual `simpleRelativeRoots i ν` into that span using `1 ⊗ α`. Its membership proof only uses the defining inclusions of simple into positive into relative roots. It asserts neither independence nor spanning.

The provenance is internal: these are scalar-extension and dimension interfaces for the actual objects, designed for the rank assertions of Borel–Tits, *Groupes réductifs* (1965), §§4.23, 4.27, 5.3 and 5.8, and Renard (French 9 July 2026), V.3.7 and V.3.12–13. The structural rank, basis, split-center and rational-character comparisons are separate propositions. In particular, no identification of the full character space with its root span is made here. No root-system existence, reductive structure theorem or standard-cocharacter existence theorem is proved by this module.
