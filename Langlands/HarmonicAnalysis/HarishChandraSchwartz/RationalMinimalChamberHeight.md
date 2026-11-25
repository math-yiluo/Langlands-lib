# Height control on the full minimal chamber in the norm kernel

This is a derived supporting module for Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, Proposition VIII.3.1,
printed p.323: the maximal-root sectors, inequality (1), and the compact
relative-rank-zero case at the start of the proof. The registered original
is `waldspurger-2003-plancherel`, DOI
[10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
The implementation uses the Library's integer `characterOrder` and its
existing positive-sign chamber convention: each simple-root order is
nonnegative. These are discrete order coordinates; the statement does not
identify them literally with the source's real logarithm coordinates.

`rationalMinimalRootSector i ν α` consists of the points `g` of the
ambient common character-norm kernel `G¹` admitting an actual torus
parameter `a` with `i(a) = g`, such that `α` is a simple relative root
and every simple-root order of `a` lies between zero and the order of
`α`. There is no restriction to uniformizer-section points.
`rationalMinimalRootSector_subset` places every sector in the full
`rationalMinimalChamberInNormKernel i ν`.

The supporting results are:

- `exists_one_add_rationalHeight_le_of_simpleRootOrders` gives a constant
  `C > 0` such that `1 + rationalHeight ρ (i(a)) ≤ C * (1 + T)` whenever
  `T ≥ 0`, all absolute simple-root orders of `a` are at most `T`, and
  `i(a) ∈ G¹`. It applies to every matrix representation with a
  nonempty finite index type.
- `exists_one_add_rationalHeight_le_of_maximal_simpleRootOrder`
  specializes this to a nonnegative maximal simple-root order. Its
  constant is uniform over the chosen root.
- `exists_rationalMinimalRootSector_cover` constructs a finite set `R`
  whose underlying set is exactly `simpleRelativeRoots i ν`, and proves
  that the union of the sectors indexed by `R` equals the full chamber
  in `G¹`, provided the simple-root set is nonempty. This result needs
  connected reductivity and maximal splitness, but no genericity.
- `exists_one_add_rationalHeight_le_on_rootSectors` expresses the
  uniform height bound using the actual ambient sector points and
  their torus parameters.
- `isCompact_rationalMinimalChamberInNormKernel_of_simpleRoots_empty`
  proves compactness of the entire chamber in `G¹` when the simple-root
  set is empty, using a closed matrix representation indexed by
  nonempty `Fin N`.

`RationalMinimalChamberHeightStatement` is a closed Prop-valued summary
of absolute root-order height control, finite sector coverage, and
empty-simple-root compactness. `rationalMinimalChamberHeight` proves it.
The absolute height estimate in this summary has no closedness premise;
the compactness implication explicitly retains closedness. The earlier
height lemmas also allow any nonempty finite index type, whereas the
summary uses the target's `Fin N` convention.

The height proof writes an arbitrary torus point as a torus norm-kernel
point times its uniformizer-section representative, using
`CocharacterUniformizer.isUniformizerLatticeSection`. The torus norm
kernel is compact by `SplitTorus.isCompact_commonNormKernel`. Its actual
image in `G(F)` supplies a compact subgroup for
`exists_rationalHeight_le_of_mem_rationalCartanCell`, with singleton
centralizer factor `{1}`. The valuation identity
`CocharacterUniformizer.mem_normKernel_mul_section_inv_iff` shows that
this representative has exactly the original character orders. Thus the
existing cell estimate applies without a Cartan covering. Increasing
the cell estimate's constant to `|B| + 1` gives a positive constant
for the height with one added.

For the cover, `relativeRootSystem` makes the simple-root set finite.
A maximum of the order function on this finite nonempty set selects a
sector for each actual chamber point. Conversely, a sector parameter
has all simple-root orders nonnegative, so it lies in the full chamber.
For compactness, the empty simple-root set makes the chamber the full
torus image. This image is closed because the maximal split torus is a
closed subgroup; intersecting it with the closed ambient norm kernel
preserves closedness. The first height theorem with `T = 0` bounds this
intersection inside a compact height sublevel, using
`isCompact_rationalHeight_le ρ hρ`.

All results retain arbitrary universes for the field, both local-field
characteristics, connected reductive groups, actual maximal split tori,
and the displayed generic cocharacters. The height does not need compact
adaptation, and no Cartan covering, Xi estimate, convergence or spectral
premise is assumed. The auxiliary compact subgroup constructed inside
the proof is not identified with any supplied special compact or
Xi-defining subgroup. This module proves the chamber geometry and height
input, not the conjugation integral estimate of Proposition VIII.3.1.
