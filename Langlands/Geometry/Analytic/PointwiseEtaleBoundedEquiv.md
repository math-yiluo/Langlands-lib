# Pointwise étaleness and bounded changes of target algebra

Author: Worker 310.

`BoundedAlgHom.isEtaleAtPoint_comp_boundedEquiv_iff` proves that, for
a finite-type bounded map `f : R → S` and a bounded algebra equivalence
`e : S ≃ T`, the composite is étale at `y` precisely when `f` is étale
at the actual comap of `y` along `e`.

Both `e` and its inverse are algebraically finite étale. One direction
is the existing pointwise composition theorem. For the other, compose
with the inverse, identify the comap point by the spectrum homeomorphism
inverse identity, and cancel the algebra equivalences. This retains
independent universes for the coefficient field and all three carriers.

This internal lemma is derived from the Library's algebraically finite
étale criterion for bijective maps, bounded spectrum homeomorphisms and
pointwise composition theorem.
