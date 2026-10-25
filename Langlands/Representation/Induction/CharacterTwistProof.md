# Character twists of smooth and compact induction

Worker 438 proves `Langlands.Induction.inductionTwist`, whose target is the
published `Langlands.Induction.InductionTwistClause` from
`Langlands.Representation.Induction.StructuralStatement`. The group and module
universes are independent. The hypotheses are precisely a group `G`, a topology
making it a topological group, a complex module `V`, and an arbitrary subgroup
`H`. The clause quantifies over a smooth scalar character and a smooth
`H`-representation. The constructions actually work without smoothness of that
input representation.

For a character `chi` and representation `sigma`, the map on functions is
`f(x) ↦ (chi(x) : ℂ) • f(x)` and its inverse multiplies by the inverse unit.
The private constructors `smoothTwistTo` and `smoothTwistFrom` use the published
`smoothFunctionOf`. Multiplicativity of the character and the original
covariance prove the new covariance under `H`. For each direction the uniform
open right stabilizer is the intersection of the original function's open
stabilizer with the character's open kernel. Thus these maps act on the actual
smooth function carriers, using one stabilizer for each whole function.

`smoothInductionTwistEquiv` bundles the forward map's complex linearity,
pointwise inverse laws, and equivariance as an actual representation
equivalence. Equivariance uses right translation and
`chi(x * g) = chi(x) * chi(g)`. Its evaluation formula and the inverse evaluation
formula are stated separately and hold by the definitions.

`quotientSupport_unit_smul` proves equality of the actual projected nonzero
supports under multiplication by arbitrary unit-valued scalars. A scalar unit
cannot turn a nonzero vector into zero. Applied to the character and its
pointwise inverse, this gives exact quotient-support equality for both
directions of the smooth equivalence. `compactInductionTwistEquiv` restricts
these same maps to the compact submodules, transporting compactness along those
equalities. Linearity, inverse laws and equivariance are inherited from the
smooth equivalence. Its evaluation formula is again definitional.

Finally, `inductionTwist` supplies both equivalences with the exact pointwise
formulas required by the existing clause. No target or imported construction is
changed. No Hausdorffness, closedness or openness of `H`, compact-open basis,
finite dimension, admissibility, irreducibility or representation-equivalence
assumption is added.

The original source is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), section 1.8(a), printed page 444 / PDF page 5,
and Proposition 1.9(f), printed page 445 / PDF page 6. Both original pages were
read for this proof. Taking their subgroup `U` trivial yields ordinary
unnormalized subgroup induction; their twist compatibility covers both smooth
and compact induction. They describe this compatibility as directly
verifiable. The explicit scalar multiplication proof above is the implemented
verification. Its arbitrary-topological-group and arbitrary-subgroup
generality is an internal extension justified by the algebraic argument,
open-kernel intersection and exact support preservation. It is not attributed
to the source's narrower `l`-group setting.

The source is registered as `bernstein-zelevinsky-1977-induced-i`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
with SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The current Library has no `notes/errata` directory.

The sole direct import is the current published structural statement module.
It imports the actual induction, smooth-part, scalar-twist and Mathlib
representation-equivalence interfaces used in the proof. This module does not
prove a determinant factorization, normalized induction in stages, half-modulus
absorption or an analytic classification result.

Development and exact-target checks use environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation is development evidence;
independent semantic acceptance and Library publication remain required.
