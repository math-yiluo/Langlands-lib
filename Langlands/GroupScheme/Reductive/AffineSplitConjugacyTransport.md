# Transport of affine split conjugacy from the ring model

Worker 591. This internal derived construction transports the affine part of
Conrad, *Reductive group schemes* (2014), Proposition 6.2.11(2), p.211,
from a ring spectrum to an arbitrary affine scheme. The reductivity of the ambient group and the split Borel
vector-series presentation on the canonical ring model remain explicit
hypotheses.

The line-bundle helper proves that triviality of every actual line bundle
passes from a scheme to any retract: pull the line bundle to the original
scheme, trivialize it there, and pull back again. The pullback composition
and identity isomorphisms identify the result with the original line bundle.
The group-point helper similarly evaluates a pulled-back base section along
a section of the base map. Its specification uses the all-test conjugating
point relation to show that the actual represented-range conjugacy holds
over the original base.

For a reductive group `G` over `Spec R`, the pair-only ring-spectrum lemma
uses the Borels containing the two tori in
their supplied `HasSplitBorelVectorSeries` presentations. Applying the
simultaneous conjugacy result and keeping its torus component gives an
actual conjugator of the two torus ranges.

Let `G` be a reductive group scheme over an arbitrary affine scheme `S`.
Then `AffineSplitConjugacy.modelTorus` is the map from
the coordinate split torus over `Spec Γ(S, ⊤)` to the pulled-back group,
using the canonical torus base-change isomorphism. Given the split Borel
vector-series presentation for this model torus, actual line-bundle
triviality, two closed split fibrewise maximal tori, and containing relative
Borels, `AffineSplitConjugacy.exists_simultaneousConjugatingPoint` produces
one actual section over `S` carrying both represented ranges to their
targets. `simultaneousConjugatingPoint` chooses that section.

The proof pulls the data along `S.isoSpec.inv`. Relative Borelness,
closedness, fibrewise maximality and range containment persist under this
base change, and the Picard hypothesis transports by the retract helper.
The ring-spectrum simultaneous conjugacy result then applies. Precomposition
by the coordinate torus isomorphisms does not change their ranges. Finally,
the point evaluation helper along `S.isoSpec.hom` gives the original-base
section with both all-test range equalities. No connectedness is required
once the model vector-series presentation has been supplied.
