# Finite Weyl models over Noetherian bases from a supplied affineness criterion

Author: Worker 640.

This draft develops a conditional Noetherian finite-Weyl construction for Task 7526.
The proposition `SelfCentralizingTorusWeylAffinenessStatement` remains an explicit
input; this module does not prove it or the parent affineness target.

The generic scheme lemma `isFinite_of_noetherian_dvr_pullbacks` proves finiteness
of a separated quasi-compact locally quasi-finite morphism locally of finite type
to a Noetherian affine base if all pullbacks to DVR spectra are finite. On a
valuative square, the finite pullback has a lift by properness; compose with the
pullback projection. The published Noetherian DVR valuative criterion gives
universal closedness. Proper quasi-finite morphisms are finite.

`isMaximalTorus_fieldPoint_of_connectedReductive_residueFibers` and
`isFibrewiseMaximalTorus_baseChange` use smoothness and affineness of each actual
residue fibre, rather than global affineness, to transport maximality. The first
proof factors a supplied field point through its canonical residue-field map,
applies the published field-extension theorem there, then transports the actual
inclusion through the iterated-pullback comparison. The second applies this
construction to every residue point of the new base.

`isAffineHom_over_dvr` applies the supplied self-centralizing Weyl criterion,
uses the finite-base/DVR etale affineness lemma on its actual quotient, and
uses the criterion's equivalence to obtain affineness of the group.

Provenance: internal composition of existing Library and Mathlib results. The
Noetherian valuative criterion's own paired Markdown records its Anthropic FLT
provenance and licence; no ported proof text is copied or modified here.

## The Noetherian finite-Weyl construction

`isFinite_suppliedWeyl_over_noetherian` applies the generic DVR test to a
supplied actual normalizer quotient. Every DVR pullback has a closed relative
torus which stays fibrewise maximal and represents its full centralizer. The
conditional DVR affineness theorem makes the ambient pullback affine. Its
connected reductive residue fibres then make it globally reductive, so the
published Weyl-quotient finiteness reduction applies to the original pulled-back
quotient. The original all-test torus-kernel condition is rewritten using the
self-centralizer representation, then transported by
`torusCentralizerKernel_baseChange`. No quotient is replaced or identified by
its cardinality alone.

`FiniteWeylModel t` stores actual normalizer and quotient group schemes, the
closed represented normalizer inclusion, smoothness of the normalizer, finiteness
and etaleness of the quotient, flat surjective locally finitely presented quotient
projection, and the all-test kernel equality with the supplied torus. Its final
field records relative affineness of the original group.

`noetherianFiniteWeylModel` constructs this data over `Spec R` for every
Noetherian commutative ring `R`, in an arbitrary universe `u`. It assumes smooth,
separated and quasi-compact ambient structure morphism, connected reductive actual
residue fibres, and a supplied closed self-centralizing fibrewise-maximal relative
torus. The construction explicitly takes a proof of
`SelfCentralizingTorusWeylAffinenessStatement.{u}` as an argument. That structural
criterion remains a separate unproved input. After the quotient is proved finite,
it is affine, and the criterion's equivalence gives the last field.

No claim for arbitrary non-Noetherian bases follows from the DVR test here.
Descending connected reductive residue fibres to a Noetherian model remains a
separate problem. This conditional construction does not prove the criterion,
provide universal torus-family existence, or prove Task 7526's unchanged target.
