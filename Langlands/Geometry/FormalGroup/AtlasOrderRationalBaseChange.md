# Coefficient extension of full-order rational formal atlas maps

This internal construction derives full-order rational coefficient extension
from the ambient tensor construction in `AtlasRationalBaseChange`, integral
order-linear extension in `AtlasOrderBaseChangeMorphism`, and the chartwise
centralizers in `AtlasOrderRationalMorphism`. It reuses the actual
`baseOrderChartIso` in `SpecialAtlasBaseChange`. No additional original-literature
assertion is made.

Let `O` and `R` be commutative rings with an `O`-algebra structure on `R`,
let `D` be a possibly noncommutative ring with an `O`-algebra structure,
and let `F` be a field with an `O`-algebra structure. The atlases `X`, `Y`
and, for composition, `Z` have finite, possibly different, coordinate types.
Their original principal covers are equal, with specified equalities `h`
and `k`, and their actions `E`, `E'` and `E''` act by actual formal
endomorphisms for every element of `D`. Coefficient algebras `S` and all
tests have the base-ring universe.

The imported base-change atlas uses the image of the original principal
cover under `R → S` and selects an original preimage generator for each image
generator. This construction allows noninjective coefficient maps.
`baseSourceOrderChartIso` equips the existing `baseSourceChartIso` with
full-order linearity in both directions. It compares the extended source
chart, transported along the equality of the image covers, with the
original source chart on the restricted coefficient test. Its coordinate
maps are the existing identity-coordinate formal comparisons. Each
commutation equation follows by formal-map extensionality, identity
composition, and `baseSourceOrderChart_coordinates`. Subtype extensionality
transports both inverse equations from the underlying actual isomorphism.

`RationalHom.baseChange_mem` shows that the ambient rational coefficient
extension of `f.val` lies in the full-order chartwise centralizer. On a test
chart, the rationalized source `baseSourceOrderChartIso.hom`, the original
`f.onChart` on the restricted test at the selected original target chart,
and the rationalized target `baseOrderChartIso.inv` form an order-equivariant
rational composite. The ambient `onChart_baseChange` theorem identifies
this composite with the extended rational map. Transporting the composite's
commutation equation along that equality proves membership for every
element of `D`. This is an equality of actual rational formal maps.

`RationalHom.baseChange` bundles the same ambient image as an `F`-linear
map between full-order centralizers. Addition and scalar preservation
follow by subtype extensionality and ambient linearity. `baseChange_val`
identifies its underlying tensor map. The theorems `baseChange_ofHom`,
`baseChange_id` and `baseChange_comp` prove agreement with rationalization
of integral full-order coefficient extension and preservation of the
rational formal identity and composition. `baseChangeRingHom` bundles
the endomorphism case as a ring homomorphism for actual composition.
`RationalHom.onChart_baseChange` gives the same source-original-target
conjugation equation inside the full-order rational coordinate centralizer;
its proof forgets the subtype and applies the ambient chart formula.

For quasi-isogenies, assume also that `O` is a domain and `F` is its
fraction field. `QuasiIsogeny.baseChange` extends both original full-order
rational maps separately. Subtype extensionality obtains both formal
inverse equations from the existing ambient extended quasi-isogeny.
The theorems `baseChange_hom` and `baseChange_inv` identify its fields,
and `toAtlas_baseChange` identifies exactly the result of forgetting
the order. Extension preserves `refl`, `symm`, `trans` and `ofIso`;
the proofs use forward-map extensionality and the rational extension
laws. `QuasiIsogeny.onChart_baseChange` expresses chart evaluation as
the source comparison, followed by the original chart quasi-isogeny,
then the inverse target comparison. Its proof uses forward-map
extensionality, the rational chart formula and composition associativity.

Full-order rational Hom here is the chartwise centralizer inside the
global tensor `F ⊗[O] BasicAtlas.Hom`, rather than the tensor of integral
`D`-linear Hom. The construction retains global finite tensor sums and the
selected preimages of the image cover. It supplies no injectivity,
surjectivity, choice-independence, successive base-change coherence or
identification with all locally rational maps. Local rational gluing,
heights, framing, polarizations, descent, levels and representability
remain separate constructions.
