# The Hom universal property of finite-etale Harris orbit covers

This internal construction gives the Hom universal property of the actual
finite-etale covers selected in `HarrisIntegralCMLevelOrbitCovers` and the
compatibility with their maps constructed in `HarrisIntegralCMLevelOrbitCoverMaps`.
It works over the same fixed actual test scheme `T.left`, with its supplied
integral-action abelian family, duality and Weil-pairing data, finite geometric
fibres, torsion finite-etaleness, invertible torsion orders and finite-etale roots
of unity. It retains connectedness and local noetherianity of the base, algebraic
closure of the point field, and explicit nonemptiness of the unchanged level tower
at one level `U`. Neither a representing scheme for the normalized moduli problem
nor an additional cover-classification equivalence is an input.

For a raw class `q` at level `V` and an actual finite-etale test cover `Y`,
`harrisIntegralCMFiniteOrbitCoverHomEquiv` is a bijection from morphisms
`Y ⟶ harrisIntegralCMFiniteOrbitCover ... q` to morphisms of finite continuous
fundamental-group actions from the geometric fibre of `Y` into the actual raw
monodromy orbit of `q`. Its forward map applies `continuousActionFunctor s hs`
and then the selected cover's action isomorphism. Its inverse takes the preimage
of an action map composed with the inverse action isomorphism.
The proved `geometricContinuousActionEquivalence s hs` supplies full faithfulness.
The functor's map-preimage and injectivity laws and cancellation of the selected
isomorphism prove that the two functions are inverse.

The `_apply` theorem identifies evaluation of this correspondence with
postcomposition of an actual geometric lift by the actual cover morphism,
followed by the previously constructed fibre bijection. The `_naturality`
theorem proves compatibility with precomposition by an arbitrary test-cover
morphism. The `_postcomp` theorem proves compatibility with any action morphism
and its previously constructed cover map, using that cover map's action
naturality equation.

`harrisIntegralCMFiniteOrbitCover_existsUnique` states the universal property
directly for functions. Any function from the actual geometric fibre of `Y`
into the raw orbit of `q` that commutes with the fundamental-group action is
realized by a unique cover morphism with the prescribed fibre function.
The proof packages equivariance as an action morphism and applies the inverse
Hom bijection. Evaluation of its right-inverse law gives existence; injectivity
of the bijection and extensionality of action morphisms give uniqueness.

`harrisIntegralCMFiniteOrbitPresheaf` is defined on the opposite of
`Cover T.left`: its value at `Y` is the type of equivariant maps from `Y`'s
geometric fibre into the same raw finite orbit. Its maps are precomposition
through `continuousActionFunctor s hs`; formally it is that functor's opposite
composed with the Yoneda presheaf of the orbit action.
`harrisIntegralCMFiniteOrbitCoverRepresents` constructs a natural isomorphism
from the selected cover's Yoneda presheaf to this presheaf. Its components
are the Hom bijections, and their precomposition law proves naturality.
The `_naturality` theorem shows that these representations respect arbitrary
orbit action maps and their selected actual cover maps.

The provenance is internal specialization of the proved finite-etale equivalence
and the preceding raw-orbit constructions. The presheaf here is defined by
equivariant fibre maps on the finite-etale cover category. Identifying it with
the unchanged raw restriction tower, extending the representation to the required
test-scheme category, and representing the full normalized CM presheaf remain
separate obligations. This unit does not prove the host division-case
representability statement.
