# Actual cuspidal tensor Jacquet quotient existence

Author: Worker 78.

`Langlands.CuspidalSupport.CuspidalTensorJacquetQuotientExistence.{uF,uV} F T`
is a derived intermediate proposition for actual integral cuspidal Jacquet-word
existence. For every positive rank and every irreducible smooth representation
on a carrier in `max uF uV`, it asks for a standard upper block parabolic whose
normalized Jacquet module has a quotient that is the actual external smooth
tensor of actual irreducible supercuspidal block representations. A quotient
means a surjective equivariant linear map in the smooth representation category.
Every block rank is positive and their sum is the ambient rank, as encoded by
`BlockShape`. The supplied compatible topological data `T` determines the field
topology and the normalized upper Jacquet action. The field and carrier
parameters `uF` and `uV` remain independent.

The proposition requires only irreducibility and smoothness. It has no analytic
square-integrability hypothesis and no admissibility, finite-length, tensor
factorization, or support-existence premise. It asserts actual quotient
realization, without imposing a common twist line on the factors.

This is internal derived content, rather than a translation of a separate
literature assertion. Its intended derivation retains the actual quotient in
`Langlands.CuspidalSupport.normalizedQuasicuspidalEmbedding_of` in
[QuasicuspidalEmbeddingProof](QuasicuspidalEmbeddingProof.md), after
`minimalNonzeroJacquet` and before Frobenius reciprocity. The additional
admissibility input is
`LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility`, and actual tensor
factorization is `padicLeviCuspidalFactorization` from
[LeviTensorFactorizationProof](LeviTensorFactorizationProof.md).
This statement does not supply any of those proofs, and no source claim about
support alone is used as actual tensor realization.
