# Support under closed pushforward

`pushforwardStalkIso` is the canonical isomorphism between the underlying
abelian stalk of the actual module pushforward at `f x` and the stalk of
the original module at `x`, when the underlying map of `f` is inducing.
It is Mathlib's presheaf stalk-pushforward map, which is an isomorphism
for an inducing map. Thus nonvanishing of these stalks agrees.

For a morphism whose underlying map is a closed embedding, the module
pushforward vanishes off its range. Every open in that complement has
empty inverse image, and sections of a sheaf of modules on the empty
open form a subsingleton. The published vanishing-to-stalk-support
comparison excludes all points outside the range. At points inside the
range, the stalk isomorphism then shows that the actual stalk support
is exactly the image of the original stalk support.

These are internal comparisons for the existing actual module
pushforward and stalk support. They require no coherence or
Noetherianness. A scheme closed immersion has the required closed
embedding, but surjectivity of its ring maps is not needed here. No
Euler-polynomial or positivity assertion is made.
