# Change of orbit base for the actual normalized standard tensor

Waldspurger V.3 formula (1) uses the forward standard operator and the
inverse of the reverse standard operator on the actual smooth dual.
VI.1 relates coefficient fibers for equivalent inducing representatives.
This module proves their generic compatibility with a change of orbit base.
The field and the carriers of both inducing objects have independent
universes.

For an equivalence between the twist of `A` by `τ` and a new base object
`B`, `compactBaseEquiv` is the existing actual compact base-change map.
It applies the inducing equivalence to the values of compact sections.
`dualBaseEquiv` uses the inverse twist `τ⁻¹` and the smooth contragredient of
the inverse inducing equivalence. `compactTensorBaseEquiv` tensors the
two fixed compact maps. `coefficientBaseEquiv` reads this same change of
base on the actual positive-Levi coefficient fibers by the published
compact tensor equivalences. When `τ = 1`, the twist-by-one isomorphism
specializes this construction to equivalent inducing representatives.

`continuedCompactSquare` uses `ActualCommonLeviBaseChange.originalSquare`
on the intersection of the two appropriately shifted starting regions.
These carry the same source-normalized radical quotient measure. Compact
restriction gives the original square in fixed carriers. The published
translated rational continuation principle propagates the equality to the
common regular values of the independent continuations and their
denominators. Nonemptiness of the actual starting overlap is explicit
input data.

For the reverse operator, the same proof uses `τ⁻¹` and `z⁻¹`.
`reverseInverseSquare` composes both sides with the particular reverse
operator, uses the reverse square and the two constructed inverses, and
then cancels by injectivity. `compactTensorSquare` tensors these squares
on pure tensors. `coefficientTensorSquare` uses the published compact
realization of the tensor to obtain the pointwise equation on all actual
coefficient vectors. Both initial overlaps and both generic memberships
remain explicit. These maps use the genuine regular loci and retain the
actual standard integral at each original base.

Source locators are Waldspurger (2003), IV.1 printed pp. 276–277/PDF pp.
42–43, V.3 formula (1) printed p. 295/PDF p. 61, and VI.1 printed pp.
295–296/PDF pp. 61–62.
