# Admissible full recognition source atlas

For an actual strong map between local-domain saturations, select every
recognized source chart whose whole image is contained in some recognized
target chart. This construction uses independent field, ambient space and
original atlas index universes. The selected source and full recognition
target have space and index universes equal to the original space universe.
All spaces are retained literally.

Every old local-domain chart is selected after singleton recognition, because
the original strong map has an admissible target for that chart. Every
recognized source chart is a finite Hausdorff special union of such old
charts. The existing contained-member quasinet on this union supplies finite
relative neighborhood refinements by old charts. Recognizing those old charts
therefore proves that the selection is locally refining. The selection is
downward closed by containment of images. The proved full-domain closure of
the full recognition atlas consequently descends to the selected source.

`recognitionMap` is the full-recognition pair system restricted to this source.
Target existence is the selection predicate itself. Its bounded maps and both
restriction variables are unchanged. The full-domain-closed source gives the
actual compatible strong map `compatibleRecognitionMap`.

`recognitionSourceComparison` maps the old local-domain source into the
selected recognition source, with identity underlying map and every canonical
original-chart restriction. Every such restriction represents its entire
relative affinoid domain, so this is a full strong quasi-isomorphism.
`compatibleRecognitionSourceComparison` retains the same map with coefficient
compatibility. The comparison followed by `recognitionMap` agrees with the
original map followed by the target full-recognition comparison as entire
strong maps. This identity uses the restriction of the constructed recognized
bounded pullback to every contained old source chart.

`recognitionSourceIndex` regards any admissible recognized source and target
pair as literal original indices of the new strong map. Its pullback is exactly
the original full-recognition bounded pullback, including its action on all
algebra elements. Thus finite recognized pieces need not be identified with a
single chart of the old atlas.

This is internal atlas infrastructure derived from the existing recognition,
subatlas, full-domain and strong-map APIs. It transcribes no external theorem.
It does not construct a global pullback or prove etale base change. Transport
of etaleness and localization comparisons is separate work, not done in this
module.
