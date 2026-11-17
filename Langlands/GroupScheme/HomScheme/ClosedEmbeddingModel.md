# Universal families of closed embeddings

`ClosedEmbeddingModel H G` consists of an actual parameter scheme over the base
and a closed group-scheme embedding after pullback to that parameter scheme.
On every test scheme its evaluated family is in bijection with the actual
closed embeddings of the pulled-back groups. The parameter map and its
naturality are consequences of this full universal property.

This is derived internal infrastructure. `ofOpen` starts with an actual
universal Hom family and an open subscheme representing precisely the
closed-immersion condition on all scheme tests. It restricts the family to
that open. Closed immersion persists under evaluation. Universality of the
original family and the actual open-immersion lift prove existence and
uniqueness of every restricted parameter, including on non-affine schemes.
No existence of such a universal Hom family or embedding open is assumed
without being supplied to this constructor.
