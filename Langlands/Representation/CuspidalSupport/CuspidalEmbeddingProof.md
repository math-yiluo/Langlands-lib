# Cuspidal embedding for actual general linear groups

Author: Worker 156.

`Langlands.CuspidalSupport.cuspidalEmbedding` proves exactly
`Langlands.CuspidalSupport.CuspidalEmbeddingTheorem.{uF,uV} F T n`
from `NormalizedCuspidalInductionStatement`. Its parameters range over every
prime `p`, every `F : PadicField.{uF} p`, every compatible topological datum `T`
and every natural rank `n`, including zero. The field universe `uF` and
representation-carrier universe `uV` are independent.

For each irreducible smooth complex representation `ω` of `GL_n(F)`, the
conclusion gives admissibility of `ω`, an actual ordered block shape `B`, an
irreducible cuspidal smooth representation `σ` of the product Levi `B.Levi`,
and an injective intertwining map into its normalized upper-parabolic
induction. Both `ω` and `σ` have carrier universe `uV`; the induced function
space may have universe `max uF uV`.

The covariance representation is exactly
`twist (T.parabolicHalfModulus B)
  (σ.representation.comp (B.leviProjection F.Carrier))`,
and the induction is the published `Induction.smoothInduced`. Cuspidality
means `IsLeviCuspidal B σ.representation`, the conjunction of admissibility
and vanishing of coinvariants for every proper standard block refinement.

## Implemented proof

The proof splits on the rank.

At rank zero it applies
`Langlands.CuspidalSupport.zeroRankCuspidalEmbedding` from
`Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof`
(Worker 157). This published boundary case has the exact required target
and independent field and carrier universes.

At rank `n + 1`, it installs the topology and topological-group structure
supplied by `T`, then performs the following assembly:

1. `Langlands.CuspidalSupport.normalizedQuasicuspidalEmbedding` from
   `Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`
   (Worker 238) supplies an actual block shape `B`, an irreducible smooth
   quasicuspidal Levi representation `σ`, and an injective intertwiner `j`
   from `ω` into its normalized induction. Positivity is `Nat.zero_lt_succ n`.
2. `Langlands.CuspidalSupport.LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility`
   from `Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof`
   (Worker 237) proves admissibility of this `σ`. Together with the
   quasicuspidality already obtained, this is precisely Levi cuspidality.
3. `Langlands.Parabolic.normalizedInductionAdmissibility` from
   `Langlands.Representation.Parabolic.NormalizedAdmissibilityProof`
   (Workers 162 and 172) proves admissibility of the actual normalized
   induced representation.
4. `Langlands.isAdmissible_of_injective` from
   `Langlands.Representation.Smooth.Admissibility.EmbeddingProof`
   transfers that admissibility to `ω` along `j`. The result permits different
   source and target carrier universes. The proof returns this admissibility
   together with the same `B`, `σ` and `j`.

Every prerequisite is imported as a published theorem. The final declaration
adds no admissibility, finite-length, countability, central-character or
embedding hypothesis. No carrier resizing occurs in this assembly.

## Source and provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §2.5, printed page 447 / PDF page 8, states the cuspidal embedding
and admissibility conclusion. Section 2.4 defines cuspidality as admissible
quasicuspidality, and §2.3(e) states preservation of admissibility by normalized
induction. Registered literature ID: `bernstein-zelevinsky-1977-induced-i`.

For `GL_n`, §2.5 refers to chapter II of Bernstein and Zelevinsky,
*Representations of the group GL(n,F), where F is a non-archimedean local field*
(1976), registered literature ID:
`bernstein-zelevinsky-1976-representations-gln`. Theorem 3.25 and Corollary
3.27, printed/PDF pages 35–36, give admissibility and the cuspidal inducing
data. These original passages were read. The rank-zero branch is an internal
extension supplied by the published trivial-group boundary proof.

This module is an internal assembly of the published normalized interfaces.
In particular, the imported Levi admissibility proof uses its documented
direct Cartan–Schur argument. The assembly does not assert that its
implementation follows the historical proof of Theorem 3.25.
