# Canonical p-adic and supercuspidal epsilon-to-gamma reduction

This internal derived unit joins the published coefficient-model and Kirillov interfaces with `EpsilonGammaLaurentReduction`. It retains the independent universes of the field and the two representation carriers. The supercuspidal Kirillov statement and the analytic Laurent input remain explicit; neither is proved here. The local converse theorem also remains open.

`Whittaker.isMirabolicTestFunction_of_supercuspidalKirillov` applies the forward support and smoothness clause of `SupercuspidalKirillovStatement` to a specified nonzero Whittaker functional and the vector representing an arbitrary coefficient-model function. The result is the existing `Whittaker.IsMirabolicTestFunction`: a uniform ambient open right stabilizer on mirabolic matrices, and compact support there modulo the actual upper-unipotent subgroup. Character covariance is converted by `mem_glFunctionals_iff_entrywise`. The assumed Kirillov bijectivity is stronger than the forward clause used by this adapter.

`PadicBlockZeroLaurentValues` records Laurent-valuedness of the existing rational-continuation value set for block `(0, r-n-1)`, when `n < r`, with canonical topology, Borel structures, normalized absolute value and residue cardinality. It quantifies over every compatible quotient measure and every pair of nonzero original functionals. It does not assert that any rational-continuation value exists, nor that a normalized generator exists.

`IsPadicPairEpsilonFactor.gammaFactor_of_laurentValues` assumes this predicate for the original pair and for the actual inverse-transpose pair with character scaled by minus one. The published nonvanishing lemmas for the dual functionals specialize the second premise to the functionals in the general Laurent reduction. After selecting the unequal-rank branches of the canonical pair relations, that reduction proves that the gamma factor is the rational epsilon monomial. The bound on the residue cardinality is the canonical proved bound.

`IsPadicPairEpsilonFactor.gammaFactor_of_supercuspidalKirillov` assembles this for an irreducible supercuspidal larger representation and a smooth smaller representation. Its second explicit input is a Laurent theorem for coefficient models whose functions satisfy `IsMirabolicTestFunction`. For the original pair, the first adapter supplies the support premise. For the inverse-transpose pair, published transport theorems give supercuspidality and irreducibility of the larger representation and smoothness of the smaller representation. The same adapter with the character scaled by minus one supplies the second support premise. Only the larger carrier's Kirillov statement is used; the smaller representation need not be supercuspidal. The resulting gamma certificate keeps every block and all quotient measures and functionals required by the original pair relation.

The provenance is composition of the published internal definitions and proved transport theorems. This module introduces no new assertion from external literature. To obtain the unconditional supercuspidal epsilon-to-gamma theorem, the Kirillov statement and the remaining compact-support-to-Laurent input must still be discharged.

The local canonical topology, valuation, field and Borel structures have
explicit module-specific instance names. Integration assigned these names to
avoid collisions when independent modules are loaded together; every instance
type and body and every mathematical declaration remain unchanged.
