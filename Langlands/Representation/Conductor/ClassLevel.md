# First nonzero levels on actual smooth classes

Worker 30 descends the published `Conductor.firstFixedLevel` to the actual
isomorphism-class quotient `SmoothDualClass`. The rank is `n + 1`, including
rank one. The integer ring and maximal ideal come from the specified
`ValuativeRel`; the actual subgroup is the published
`Conductor.levelSubgroup F n a`.

The representation-equivalence lemmas preserve existence of a nonzero level,
the least-level characterization including all lower vanishing conditions,
and the total `WithTop Nat` value. The proof of total-value invariance
separates existence from nonexistence: in the first case uniqueness of the
intrinsic conductor gives equality, and in the second both values are infinity.
These arguments retain independent coefficient, local-field and two module
universes. They do not require finite dimension, irreducibility, admissibility,
genericity or smoothness of the input representations.

The class function uses `Quotient.lift` and the actual equivariant linear
equivalence underlying an isomorphism. Its evaluation on `ofRep` is
definitional. The theorem `firstFixedLevel_le_iff` is proved first for
representations and then on classes: a finite bound `b` is equivalent to
nonzero invariants under the level-`b` subgroup. Its forward implication uses
monotonicity of fixed spaces; its converse uses minimality of the first
nonzero level. Infinity cannot satisfy a finite bound.

`centralLevelStratum` fixes scalar action of the prescribed character of the
actual center and imposes this finite bound. It contains actual irreducible
admissible isomorphism classes. No finiteness assertion is made for all those
classes here; the supercuspidal restriction is a separate construction.

This is an internal quotient construction from Jacquet, Piatetski-Shapiro and
Shalika, *Conducteur des representations du groupe lineaire* (1981),
Section 5.1, page 211, parts (ii)--(iii), as realized by the published
`Langlands.Representation.Conductor.Definitions`. Source ID
`jpss-1981-conductor`, SHA256
`986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
The original pages 199--202 and 210--214 have been read.
The theorem's irreducible generic complex scope, additive-character conductor
zero, and level-zero convention remain as documented there.

The general epsilon-factor conductor is not defined by this function.
Finite-level existence, supercuspidal genericity, equality with the normalized
epsilon exponent, and the newvector dimension theorem remain separate
theorem obligations. In particular, the warning in JPSS Section 5.4,
page 214, is retained: arbitrary smooth irreducibles need not have finite
last-row level. This module makes no essential-vector claim and does not
use the original essential-vector existence argument corrected in 2012.

Imports are the companion `Category.ClassInvariants` and published
`Conductor.Definitions`; the latter imports the actual congruence construction.
No pending theorem is stored as a construction field. The invariance and
finite-bound characterizations are proved as intrinsic construction obligations.
