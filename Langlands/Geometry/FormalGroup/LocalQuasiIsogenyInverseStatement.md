# Inverses of actual local quasi-isogenies: proof boundary

`Langlands.FormalGroup.ModuleLaw.LocalQuasiIsogenyInverseStatement` is an
internal unproved proposition. It isolates the missing inverse construction
for the existing actual rational-sheaf local quasi-isogenies.

Fix a commutative ring O, a commutative O-algebra R, an O-algebra field F,
a scalar pi in O and two formal O-modules M and N with finite coordinate
types. R and F share a universe, while O may have a different universe.
For every open U and every `LocalQuasiIsogeny F pi M N U`, the target
requires a unique `RationalSectionIso F M N U` with that same forward
section, whose reverse section also satisfies the pointwise local
scalar-isogeny condition for pi.

The input local quasi-isogeny already retains pi being nonzero in F and
both M and N being pi-divisible in the existing affine sense. In particular
pi acts nilpotently on R, every actual test-algebra point is killed by
some scalar power, the scalar map has affine fppf local lifting, and every
scalar-power kernel has an actual finite projective representing algebra.
The input forward section itself is locally a pi-power denominator of an
actual integral isogeny. Its witnessing exponent and neighbourhood may
vary with the base point. No global denominator, integral numerator or
inverse section is supplied.

The conclusion's `RationalSectionIso` contains actual forward and reverse
sections, with both composites equal to the actual identity sections.
Its additional predicate requires the reverse section locally to be a
scalar multiple of an actual integral isogeny, rather than only an abstract
one-sided inverse. This is enough to construct a reverse local
quasi-isogeny after the theorem is proved. The uniqueness concerns these
actual section objects, not a choice of integral witnesses or denominators.
It is compatible with the already proved uniqueness from a forward section.

An anticipated proof must produce integral inverse numerators locally
using the scalar-divisibility and actual finite-kernel hypotheses, prove
their isogeny condition, and glue the resulting rational inverse sections.
Uniqueness can identify these sections on overlaps, and the actual sheaf
condition can then glue them. These steps are requirements of the future
proof, not implemented arguments in this statement module.

This target is an internal prerequisite for the parent moduli
construction. It is not presented as a quotation of a numbered theorem
from the original literature. It asserts no converse saying every
invertible rational section is a local quasi-isogeny under these general
coefficient hypotheses. No fraction-field, discrete valuation or
uniformizer hypothesis is used; pi may be any scalar satisfying the
existing input conditions. Nilpotent rigidity, arbitrary coefficient
base change and representability are different open obligations.
