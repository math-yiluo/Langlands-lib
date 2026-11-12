# Common candidates and stable images

Author: Worker 4803. Module `Langlands.Correspondence.HenniartStableImage`,
namespace `Langlands.Henniart.StableMap`.

Elementary consequences of the published definitions of
`Langlands.Henniart.StableMap.IsCandidate` and `IsStableImage` (module
`HenniartStableMapStatement`). Nothing from the literature is assumed. These
lemmas are used by the §4.4 extension in `HenniartExtension` and its sibling
modules.

## Monotonicity in the quotient

`unitaryFiniteFactoringSupported_comp_le`: a unitary class factoring through
`f ∘ q`, for `q : Gal(K̄/K) →* Q` and `f : Q →* R`, factors through `q`. A
witness `A` for `f ∘ q` gives the witness `A ∘ f` for `q`. The representation of
the composite is the same, so the class equation is unchanged.

`IsCandidate.comp`: a candidate at `q` is a candidate at `f ∘ q`. Its domain
contains the classes factoring through `q`, hence those factoring through
`f ∘ q`, and the properties of 3.8 do not mention the quotient.

## Evaluating stable images

`IsStableImage.exists_quotient` unpacks a stable image `y` of `σ` at its own
quotient `q`. For every quotient `r` (in the field universe) and every `f` with
`f ∘ r = q`, and every candidate `Φ` at `r`, the generator of `σ` lies in the
domain of `Φ` and `Φ` sends it to `y`. Such a `Φ` is a candidate at `q` by
`IsCandidate.comp`, and the definition of `IsStableImage` applies.

`exists_common_candidate`: assume candidates exist at every finite quotient
(`CandidateExistenceStatement` with quotient universe `uK`). Given finitely many
classes `σ i` with stable images `y i` (index type `ι : Type` finite), the product
quotient `MonoidHom.pi q : Gal →* Π i, Q i` has a candidate `Φ`. Its composite
with each evaluation `Pi.evalMonoidHom` is `q i`, so `Φ` sends each `σ i` to
`y i`. Only the Henniart properties of `Φ` are retained.

`IsStableImage.unique`: two stable images of the same class agree. Apply the
previous lemma to the two-element family indexed by `Bool`; the two domain
elements are equal, so their images are equal.

## Shape of stable images

`LocalWeil.unitaryDegree_generator` and `PadicSupercuspidal.unitaryDegree_generator`
compute the published integral degrees on generators: the rank.

`IsCandidate.exists_generator`: a map with Henniart's properties sends a
generator in its domain to the generator of a unitary supercuspidal class of the
same rank. Use the generator clause of 3.8 (`LatticeMap.GeneratorCompatibility`)
and the degree clause of the isometry property.

`IsStableImage.exists_generator`: a stable image is the generator of a unitary
supercuspidal class of the rank of the Weil class. Use the candidate supplied by
`IsStableImage`.

`IsStableImage.isFiniteFactoring`: a class with a stable image factors through a
finite quotient. This is part of the definition.
