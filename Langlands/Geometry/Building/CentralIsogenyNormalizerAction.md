# Actual normalizer derivatives in a central-isogeny square

Author: Worker 1631.

This internal derived unit works over any field `k`, in arbitrary universe `u`.
Supply a commuting square `i ≫ q = groupHom t ≫ j` from split acting tori
`S`, `T` into ambient groups `C`, `G`. The actual map `t` is an isogeny and
the target embedding `j` is a monomorphism on underlying schemes.

`splitTorusIsogenyNormalizerMap` is the actual map from source normalizers to
target normalizers. It applies the fppf acting-group descent construction
`TorusCoverTransport.normalizerPointsMap`. Flatness and surjectivity come
from the isogeny, while local finite presentation follows from the published
`locallyOfFinitePresentation_of_splitTori`. The underlying rational point
is composition with `q`, with no assumption that `q` is an isogeny or
surjective on rational points. The source and image normalizer automorphisms
commute with `t` by the descent comparison.

When `i` is also a monomorphism on underlying schemes, actual real
cocharacter postcomposition intertwines the source normalizer action with
the action of this actual image normalizer. Tensor induction reduces this
to the proved torus-automorphism square on integral cocharacters.

When the ambient groups are affine and locally of finite type and `q` is a
central isogeny, `centralIsogenyTranslationEquiv_translationAction` says
that the previously constructed reduced translation equivalence intertwines
the actual quotient derivatives. Quotient induction reduces this to the
cocharacter identity. Both normalizer actions are the original Library
actions; no action is introduced as an extra input.

The provenance is the existing Library split-torus finite-presentation theorem
and normalizer descent argument, together with the internally derived generic
fppf normalizer transport and translation comparison. Cover tori and their embeddings remain supplied geometric data.
This unit constructs no map of valuation apartments and asserts no apartment
axioms or final normalizer-image theorem.
