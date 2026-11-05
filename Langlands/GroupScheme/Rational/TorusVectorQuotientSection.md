# Complementary quotient sections from torus retractions

This internal derived unit combines actual fpqc homomorphism descent with
the original-field torus retraction constructed in
`TorusVectorRetractionDescent`. It supplies a complementary quotient
section for the characteristic-zero rational-point factorization.

For an arbitrary base scheme `S`, a commutative group scheme `E`, a
monomorphism `z : Z ⟶ E`, and an actual fppf quotient `p : E ⟶ Q` with
kernel `range z`, suppose `r : E ⟶ Z` satisfies `z ≫ r = 𝟙 Z`.
The projection is explicitly required to be quasi-compact.
`exists_section_of_retraction` constructs an actual homomorphism
`s : Q ⟶ E` satisfying
`p ≫ s = 𝟙 E / (r ≫ z)` and `s ≫ p = 𝟙 Q`.
`sectionOfRetraction` chooses this morphism; the two associated theorems
record its identities. No commutativity assumption on `Q` is needed.

The complementary endomorphism is an actual group homomorphism because
`E` is commutative. Its restriction to `Z` is trivial by the retraction
identity. The quotient's actual kernel is identified with `Z`, which shows
that the complementary endomorphism kills the full scheme kernel.
Flatness, surjectivity and quasi-compactness allow fpqc homomorphism
descent. Its factorization identity supplies the first displayed equation.
Composing that equation with `p` gives `p`, since `z ≫ p` is trivial.
Equality out of the quotient can be checked after precomposing with `p`,
so the second displayed equation follows. This argument uses actual
scheme quotients and does not assume surjectivity on field-valued points.

Over any field `k : Type u`, `exists_split_of_vector_quotient` applies this
construction to a commutative affine group scheme with a specified closed
central torus inclusion and a finite-dimensional vector-group quotient.
It returns both a torus retraction `r` and a quotient section `s`, with
the three identities above. The quotient's vector coordinates supply
affineness, hence quasi-compactness of the projection. The nonsplit
retraction theorem supplies `r` over the original field. The result has
no perfection or characteristic hypothesis; the vector quotient is an
explicit premise.

The final rational-point factors remain a separate application of these
identities and a line through a point in a vector group.
