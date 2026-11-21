# Leading derivatives along a vanishing vector field

`Langlands.HarmonicAnalysis.VectorFieldLeadingJetStatement` computes the
order-`k` jet of the derivative of a smooth function along a smooth vector
field at a zero of the field. If the function's lower derivatives vanish,
the result is the sum of the order-`k` jet with the field's linearization
applied in each slot in turn. If that linearization is nilpotent, the slot
sum has a common nilpotence exponent depending only on `k` and the domain
dimension. A companion lemma shows that multiplication by a smooth scalar
vanishing at the point contributes zero to the leading jet.

The Lean proof first uses a bump to reduce to a globally smooth field germ.
It differentiates the pullback by `y ↦ y + t • V y` at `t = 0`. The mixed
iterated derivatives commute by permutation symmetry on the product of the
parameter line and the domain. Because the lower function derivatives vanish,
the composition rule for the order-`k` derivative uses only the first
derivative of the pullback map. Differentiating its multilinear evaluation
gives the sum of the slot actions. Distinct slot actions commute, and taking
a power within one slot applies the corresponding power of the linearization.
Cayley–Hamilton bounds that power by the domain dimension. Finite induction
then gives the stated power of the sum. The multiplier lemma uses the
iterated product derivative bound, in which each summand vanishes.

This internal calculus result supplies the leading derivative calculation for
distributions supported on a product zero section.
