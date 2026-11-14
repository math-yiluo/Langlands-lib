# A bounded conjugation grid forces split-torus commutation

This internally derived helper applies constancy of bounded split-torus maps to
the conjugation morphism. If the conjugates of a fixed rational point by all
integer-power tuples of a unit lie in an algebraically bounded set, and that unit
has nonzero logarithmic integer valuation, every rational point of the split
torus commutes with the fixed point. The target group scheme is affine.

The implemented proof constructs the morphism as the product of the torus
homomorphism, the constant fixed point, and the inverse homomorphism on the
underlying schemes. Precomposition evaluates this morphism as conjugation.
Algebraic boundedness supplies the coordinate bounds needed by
`tuplePoint_comp_eq_of_bounded`. Its value at the identity tuple is the fixed
point itself, so constancy is exactly the commutation assertion.
