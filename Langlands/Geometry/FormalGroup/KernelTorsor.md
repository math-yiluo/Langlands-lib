# Translation of a represented kernel fibre

This internal construction identifies a represented kernel fibre with
the zero fibre after a lift of its universal target point has been
chosen. The translations are addition and subtraction of the chosen
actual formal-module point.

Let f and h have finite projective actual kernel representations and
let f composed with g equal h. The coordinate map from the algebra of
ker f to the algebra of ker h is obtained by applying g to the
universal ker h point. A coefficient-algebra map from the former
algebra, together with an actual ker h point lifting its represented
ker f point, specifies a fibre and a translating point.

The quotient from `KernelQuotient` represents the zero fibre, ker g.
Translation by the chosen lift is a natural bijection between that
zero fibre and the specified fibre. The inverse subtracts the lift.
The construction uses the genuine kernel corepresentations and
actual point-functor operations throughout.

The tensor algebra of the zero-fibre algebra and the cover is proved
to be the pushout of the represented kernel-algebra map along that
cover. Its universal property is checked by translating the associated
points, and uniqueness follows from injectivity of translation and
the two-factor universal property of the tensor product. The
forgetful functor to commutative rings preserves this pushout.
Consequently flatness of the cover map implies flatness of the
translated fibre map by base change.

This is internal infrastructure for the finite locally free kernel
obligation of integral dual isogenies. It is not a quotation of a
numbered result in external literature.
