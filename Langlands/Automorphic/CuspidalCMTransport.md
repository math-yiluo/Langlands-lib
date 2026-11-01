# Actual CM pullback on cuspidal automorphic forms

Worker 2. Internal restriction of the actual `AutomorphicForms.complexConj`
from `AutomorphicCMTransport` using the constant-term covariance proved in
`ConstantTermArithmeticTransport`. No new original-literature identification
or occurrence assertion is made.

Let `K : Type uK` be an actual CM number field and let `n` be any natural
rank. The compactness of the actual additive adele quotient is an explicit
instance parameter, as in the existing `CuspidalForms` spaces. The complex
values of forms are fixed; conjugation acts on the argument by the actual
CM adelic matrix map.

`AutomorphicForms.complexConj_mem_cuspidal_iff` preserves and reflects the
existing vanishing condition for every normalized constant term.
`complexConj_mem_centralCharacterCuspidal_iff` combines this with the proved
central-character correspondence on the same actual form. The transported
character is `HeckeCharacter.complexConj`, namely precomposition with CM
conjugation on idele classes.

`CuspidalAutomorphicForms.complexConj` restricts the existing continuous
complex-linear equivalence to the actual cusp subspace. The image equality
is proved from the membership biconditional and surjectivity of the
automorphic equivalence. The restriction is involutive and equals its
inverse. Evaluation, covariance of the actual finite adelic right action,
and compatibility with the existing inclusion into all automorphic forms
are proved.

`CentralCharacterCuspidalForms.complexConj n chi` similarly gives a genuine
continuous complex-linear equivalence from the `chi` cusp space to the
`chi.complexConj` cusp space. Forward and inverse evaluation both precompose
with the actual CM adelic map. Its finite adelic covariance and inclusion
compatibility follow from those of the ambient automorphic equivalence.
All topologies are the existing subspace topologies inherited from
compact-open continuous functions; no topology on derivatives is added.
