# Scheme quotients from maps with exact relation fibers

Author: Worker 148.

This derived internal module combines the published canonical smooth-relation
quotient, its elementary descent maps, and the published scheme-representability
theorem for algebraic spaces with a locally finite type monomorphism into a
scheme. Its provenance is those universal properties, rather than a new external
geometric input.

All constructions use actual schemes over an arbitrary base `S` at arbitrary
universe `u`. The arrow algebraic space `R` is a monomorphic equivalence relation
on all sections of the scheme `U`, with the existing endpoint maps and relation.

`mono_quotientPresheafDesc` shows that an endpoint-constant natural transformation
whose sectionwise kernel is exactly the relation descends to an injective map
from the pointwise quotient. The proof takes representatives and uses the exact
kernel criterion to obtain equality of quotient classes.
`mono_quotientSheafDesc` proves that the corresponding descent from the canonical
etale sheaf quotient is a monomorphism when the target is an etale sheaf.
The proof uses preservation of monomorphisms by the left exact sheafification
functor and identifies the target with its own sheafification.

`exists_scheme_quotient_of_map_kernel` assumes smooth relation projections, local
finite type of `U` over `S`, and an actual scheme map `r : U → Y` whose fibers on
every scheme test are exactly the relation. The published quotient theorem
provides an algebraic space with a smooth surjective presentation by `U` and a
locally finite type etale atlas. The descended map to `Y` is a monomorphism by
the preceding lemmas. Its atlas composite is locally of finite type because
the atlas is locally of finite type over `S`. The published monomorphism
theorem therefore represents the quotient by an actual `Q : Over S`.
Full faithfulness of scheme Yoneda constructs `q : U → Q` and `j : Q → Y`,
with `q ≫ j = r` and `j.left` monomorphic. A pullback against the representing
isomorphism proves that `q.left` is smooth and surjective. Cancellation of `j`
gives exactly the stated all-test relation fibers of `q`.

`SchemeQuotientEmbedding` retains this actual scheme, its projection and ambient
embedding, their factorization, the monomorphism, smoothness and surjectivity
proofs, and the full fiber criterion. `schemeQuotientOfMapKernel` chooses this
data by classical choice from the existence proof. This is an actual scheme
model with morphisms, rather than a new predicate asserting representability.

The theorem is conditional on the existence of `r`. It does not construct a
group representation or a stabilizer embedding, and alone does not prove the
unconditional smooth-subgroup quotient existence statement. It makes no
separatedness or quasi-compactness claim about `Q` or `q`.
