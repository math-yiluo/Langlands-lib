# Finite families of discrete restrictions after shrinking the base

Suppose ordinary points lift along covering sieves in the analytic étale site,
and the supplied family of deck automorphisms acts transitively on each fibre
of an étale object over its base. For a finite family of sections of an étale
G-sheaf and a point of the object, there is an open neighbourhood of the image
point and a single finite family of arrows in every section's discrete sieve.
The family becomes covering on the object's restriction to any smaller open.

`deckTranslateDiscreteSieve` intersects the discrete sieves for all deck
translates of the given sections. This intersection is covering for finite
section and deck families, so the point lifts along it. The source of the
chosen arrow is étale over the base, so its image contains an open
neighbourhood of the image point. All deck translates of the arrow lie in
each original discrete sieve. Over any smaller open, every point of the
restricted object has the same base image as some point in the restricted
source of the chosen arrow. Deck transitivity gives one of the finite
translated arrows over that point.

If the original object and the smaller object are both distinguished and
carry lifts, `TwistedFiniteRestrictionSections` makes the restricted
sections discrete for the smaller lift. It applies using the original
discrete-sieve witnesses and the covering family after pullback.

This internal shrinking argument uses the open restriction functor on the
ordinary étale site and the discrete sieve of a section on the twisted site.
