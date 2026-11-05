# Generic-fiber adelic comparisons for specified arithmetic model cones

`Langlands.Global.adelicSpreadModelPullback` proves exactly
`Langlands.Global.AdelicSpreadModelPullbackStatement` at arbitrary common
universe `u`. It proves both arithmetic clauses with the target's original
finite-type models, separatedness of the base model only, specified
pullback cone, actual generic-fiber pullback functor, actual full adelic
rings and existing spread topologies. No descent of a new field cone is
assumed or proved by this unit.

The internal lemma `isHomeomorph_imagePullbackPointComparison` applies to
any functor between the two relevant categories of schemes over ring
spectra and a natural family of homeomorphisms on their actual points.
The family of target topologies is indexed by the original models; it
requires no injectivity of the functor on objects or choice of a model for
every target object. The product of the homeomorphisms on `X` and `Y`
restricts to a homeomorphism between the two compatible-pair subspaces.
Naturality expresses each compatibility equation as the image of the
original equation on base points; injectivity of the homeomorphism on
`Z` gives the equivalence of these conditions.

The lemma composes the inverse homeomorphism on source points, the
original pullback-comparison homeomorphism and this compatible-pair
homeomorphism. Equality with the image cone's actual point comparison is
proved component by component. Both equalities use naturality along the
cone legs and the inverse identity for the source point homeomorphism.
Thus the product and subtype topologies remain precisely the specified
ones throughout.

The function-field branch specializes this lemma to the actual pullback
along the outside-`S` integer inclusion into `F`. Its homeomorphisms are
`curvePlaceSpreadAdelePointHomeomorph` with identity generic-fiber
isomorphism, and their naturality is
`curvePlaceGenericFiberAdelePointEquiv_natural`. The original comparison is
the function-field clause of `adelicFixedModelPullback`.

The number-field branch uses the corresponding number-field constructions
and that theorem's second clause. It explicitly installs the original
integer-base algebra structure of `numberFieldAdeleOver` and the existing
`K`-algebra structure on full `Adeles K`, so all infinite factors and the
actual scalar action are retained.

This is the implemented transport argument for the derived comparison
associated with Conrad (2011), printed pp.8–9, as specified by the unchanged
target Markdown. It introduces no local compactness, finite-residue-field,
additional separatedness, affineness or function-field separability
premise. The perfectness of the arbitrary curve constant field is exactly
the target premise inherited from its generic-fiber point constructions;
empty initial place sets are allowed. Arbitrary independently given field
cones, spreading them with a separated base model, and independence from
arbitrary alternative spreads remain separate whole-paper obligations.
