# Outer quotients from constant families of representatives

This internal derived construction applies the existing all-test normalized
section constructor to a family indexed by the constant scheme of an arbitrary
type `D`. The base scheme and every test scheme are arbitrary.

`GroupIsomorphismScheme.constantParameter S D` is the scheme coproduct of one
copy of `S` for each element of `D`, with the identity structure morphisms.
The coproduct separatedness theorem proves that its structure morphism is
separated. Étaleness and local quasi-finiteness follow by Zariski locality at
the source, since each component map is an identity. Its structure morphism
is also locally of finite type.

For a supplied isomorphism scheme `I`, an automorphic action `a`, and an actual
family `s` from this constant parameter into `I.parameter`,
`outerOfConstantSection` assumes that the orbit map gives a bijection on every
relative scheme test. It invokes `outerOfNormalizedSection`, whose Yoneda
argument identifies the isomorphism scheme with the product of the acting
group and the constant parameter. Flatness and quasi-compactness of the acting
group give the corresponding properties of the class morphism; its
surjectivity and unique same-test discrepancy are supplied by the product
constructor.

The resulting outer quotient has exactly the constant scheme as its parameter.
The module exposes its separatedness, étaleness, local quasi-finiteness and
local finite-type property as instances. The label type need not be finite or
nonempty. Scheme-valued points of the coproduct allow labels to vary locally,
so the assumptions do not replace a family on a disconnected test by one
global label.

The construction is an internal specialization of published scheme-coproduct
geometry and the supplied normalized-section constructor. It does not prove
existence of the family or its all-test bijection, classification of pinned
models, or the generic DVR outer-isomorphism existence statement.
