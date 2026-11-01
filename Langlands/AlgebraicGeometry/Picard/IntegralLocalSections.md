# Integral separated morphisms with local sections

These internal derived lemmas support the birational unramified criterion. They
use the already implemented open-diagonal argument for sections of a locally
finite type formally unramified morphism.

A section over a nonempty base open factors through the inverse image of that
open. This factored section is an open immersion by unramifiedness and a closed
immersion by separatedness. Its image is nonempty and therefore dense in the
integral inverse-image open. Its image is also closed, so it is surjective and
an isomorphism. Consequently the original morphism is an isomorphism over this
base open.

If every source point admits a section around its image, the previous argument
makes the morphism injective and locally an open immersion on its source. The
source-local criterion then makes the full morphism an open immersion.

Finally, if the base is integral and all stalk maps are isomorphisms, their
inverses define sections over the spectra of the base stalks. Mathlib's spreading
construction extends these to sections on neighborhoods of the base points,
retaining the equation over the base. This supplies the preceding hypothesis.
