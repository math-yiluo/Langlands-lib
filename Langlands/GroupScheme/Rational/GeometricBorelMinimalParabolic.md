# A geometric Borel is a minimal rational parabolic

This internal comparison uses only the existing definitions of geometric Borel
and parabolic subgroups and fpqc reflection of group-scheme isomorphisms.
There is no assumption of finite ground field or reductivity of the ambient group.

`IsGeometricBorelSubgroup.parabolicFactorIso` constructs an actual isomorphism
from a parabolic subgroup into a geometric Borel whenever the given parabolic
embedding factors through that Borel. Over the algebraic closure, a Borel
inside the parabolic factors into the specified geometric Borel. Borel
maximality makes this composite an isomorphism. The parabolic-to-Borel map
is monic because both are subgroup presentations, and the isomorphism gives
it a section. It is therefore an isomorphism over the algebraic closure.
Faithfully flat base change reflects that isomorphism to the ground field.
The isomorphism's forward map is exactly the supplied factor.

The two minimality theorems factor any all-test range inclusion through the
closed Borel embedding, apply this constructor, and conclude equality of
ranges. Thus every field-defined geometric Borel is a minimal rational
parabolic subgroup and its range is a minimal rational parabolic functor.
This is a derived comparison of published definitions, rather than a new
existence or conjugacy theorem.
