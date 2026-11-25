# Outer parameter geometry from local normalized families

Internal derived material for the outer-parameter clauses of
relative reductive automorphism geometry. An actual full Isom representative
and an exact outer quotient are supplied. The acting group is flat and
locally of finite presentation.

`parameter_property_of_etaleCover` transfers a morphism property from the
parameters of complete normalized local families to the structure map of
the outer parameter. It applies to any property that is stable under base
change, local at the Zariski target, and satisfies fppf target descent.
The input is an actual étale covering family of the base. Each normalized
family retains its original-base scheme parameter, its projection to the
cover member, and its unique orbit decomposition on every original-base
test. The previous local quotient comparison identifies that parameter
with the pullback of the outer parameter over the cover member. Fppf
locality of the morphism property then gives the conclusion.
The comparison uses the supplied local finite presentation proof for the
actual class map, with fpqc descent as its default.

`geometry_of_localConstants` specializes to normalized parameters that are
possibly infinite disjoint unions of copies of the local base. It proves
that the supplied outer parameter is separated and étale. It also returns
the actual local isomorphisms in the appropriate slice category. The same
class-map proof serves both property descents and the local isomorphisms.

No outer quotient or full Isom representative is constructed in this
module. The normalized families are substantive explicit inputs. The
cover, its index type, the bases, and all tests are arbitrary in each
universe. No global quasi-compactness or finiteness of outer components
is asserted or assumed.

`constantLocalParameterIso` chooses, on every member of the given cover,
the label type and an actual local comparison isomorphism obtained from
the proved geometry. It retains the same normalized-family hypotheses.
