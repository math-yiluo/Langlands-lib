# Compatible full-map descent after an actual source refinement

This internal construction extends the existing full strong-map domain
descent with compatible-map restriction and exact projection recovery. The
field, space, index and cover-index universes are independent.

Direct restriction of an original compatible map to a smaller actual source
domain retains every bounded pullback and its coefficient coherence. It
commutes with complete compatible composition and with ambient source
restriction.

Given a full strong matching family on an original-domain quasinet cover,
source saturation supplies the compatible structures on its local maps.
`compatibleRefinedGlue` uses the existing constructed source selection and
full strong glue. Downward closure plus the original source saturation
proves saturation of this selected source atlas, hence compatibility of the
entire glued map. No global map or output source selection is supplied.

The point and bounded-pullback recovery theorems follow from the existing
full restriction identity of the glue. For a compatible projection of the
local matching family, `compatibleRefinedGlue_comp` proves equality of the
entire global projection composite with the original ambient map restricted
to that selected source atlas. The proof chooses a covering member for each
selected source chart, computes the complete composite through a local
target chart and uses the unchanged original local bounded map. Base maps
are compared using the actual domain quasinet cover.

No local matching or covering property is inferred for an arbitrary family.
They are explicit inputs. This is a general descent helper, not the final
localized etale pullback or etale base-change theorem. No external statement
is transcribed.
