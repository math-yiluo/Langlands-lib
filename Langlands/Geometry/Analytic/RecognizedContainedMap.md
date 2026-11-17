# Full bounded squares for contained recognized subsets

This internal lemma compares the constructed full-recognition pair system with
original bounded pullbacks when the two recognized loci lie in an admissible
pair of original charts of the saturated presentations. It proves the complete
bounded equation after composition with the contained-domain structural maps.
No equality of algebra maps is inferred from their ordinary-point functions.

The proof first verifies compatibility of a recognized restriction with the
contained-domain structural maps, by descent to every original source chart.
It then uses the recognized original target chart as an intermediate chart.
The pair-system restriction law and its recovery of original bounded pullbacks
reduce the square to the original strong-map restriction law. The constructed
maps in `RecognizedContainedDomain` retain all algebra elements, so these are
identities of entire bounded homomorphisms. This is a prerequisite for comparing
recognized inverse-image maps with actual affinoid pushout legs; no finiteness,
étaleness, or unrestricted pointwise lifting is asserted here.

The same source also constructs `StrongHom.fullRecognitionPullbackEquiv`. Given
a recognized inverse image inside an admissible original chart pair, both its
contained domain and the actual affinoid pushout represent the same literal
subset of the source chart spectrum. Their full universal properties construct
a bounded algebra equivalence, preserving the original structural map.
The target contained domain's universal property then proves that the complete
full-recognition pullback equals the original second pushout leg followed by
this equivalence. The inverse-image equality is an explicit premise; this
module does not yet establish the existence of recognized inverse images.
