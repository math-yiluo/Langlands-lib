# Full field-point pullbacks over finite original chart pairs

This is an internal deduction from the actual localized field-point functor,
the bounded affinoid pushout, and faithful local field-point representatives.
The base field `K : Type u` is complete and ultrametric. The space and chart
index universe `v` and the normed extension field universe `uL` are independent.
The supporting construction assumes that `L : Type uL` is complete and
ultrametric, with its given `NormedAlgebra K L` structure; algebraic closedness
is not needed. Domain completed-residue comparison remains an explicit premise.

`HasFiniteChartPairs f g` says that every compatible pair of ordinary points
admits original containing source charts `i`, `j`, a common original target
chart `t`, and chart admissibility for both maps, such that the actual first
bounded chart pullback is finite Banach. This predicate does not assert that
all strong etale cospans have such pairs in their original atlases.

The initial identities compute the descended functor on localized strong maps
and extract equality of the entire iterated field-point images from a localized
commuting square. Compatible full points therefore give compatible actual
bounded evaluations on any admissible selected chart pair. The small-spectrum
chart-map composition formula retains the original bounded composite, and its
membership lemma puts every image point in the selected original chart.

`existsUnique_fieldPoint_lift_of_small_pair` assumes a supplied genuine
localized pullback square of four strong maps, a compatible pair of full field
points, containing original source charts, a common admissible target chart,
and `Small.{v}` for the spectrum of their actual bounded affinoid pushout.
It proves that the pair has a unique full field point in the supplied vertex.
No strict commuting square of the original strong maps is assumed.

For existence, the compatible evaluations give a bounded character of the
actual affinoid pushout. The conditional all-chart extension gives its full
field point. The two chart-source maps give a strict strong cone, since their
original bounded composites agree by the pushout relation. Their full images
are the prescribed full points. The supplied localized universal property
then carries this cone point to a full field point of its vertex.

For uniqueness, each candidate point is represented on one actual containing
chart by its faithful kernel quotient, chosen admissible to both fixed image
charts. Equality of its two complete nested images, obtained from localized
commutativity, makes the quotient-valued pullbacks compatible. The actual
bounded pushout thus maps to this quotient. Its composite with the injective
quotient character equals the fixed pushout character by the two projection
equations and bounded pushout uniqueness. Consequently the entire faithful
point maps to the fixed pushout point. Equality of the resulting full images
in a common chart detects equality of the complete strong morphisms to each
side. Localized pullback uniqueness identifies the representative map to the
vertex with its factorization through the fixed cone lift. Applying the actual
descended functor proves equality of all full field-point data.

`existsUnique_fieldPoint_lift_of_finiteChartPairs` additionally assumes
`FiniteBanachPushoutStatement K` and `HasFiniteChartPairs f g`. It selects the
charts at the ordinary underlying points. The second chart spectrum is
`v`-small by its embedding in the original presentation, and finite Banach base
change makes the actual pushout spectrum `v`-small. The preceding theorem
then gives the unique full lift.

`fieldPoint_isPullback_of_finiteChartPairs` proves preservation of the supplied
localized square by the actual `localizedFieldPointFunctor L`. Commutativity
is functoriality; joint injectivity and compatible-pair existence both follow
from the full-point unique-lifting theorem. The pullback is in types of the
functor's actual universe, with no identification of `u`, `v`, and `uL`.

The argument uses `FieldValuedPoints`, `AffinoidFieldCharacters`,
`GlobalChartSourceMaps`, Worker 659's faithful local representatives and
`FieldPointRepresentativePointPushout`, and
`GeneralizedAffinoid.FiniteBanachPushout.Statement`. It is a supporting result:
the two algebraic comparison statements and the finite original chart-pair
condition remain explicit. It does not by itself prove the unconditional
localized etale field-point preservation target.
