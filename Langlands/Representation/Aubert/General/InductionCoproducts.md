# Coproduct comparison for normalized induction

Author: Worker 1187. Internal category infrastructure for the induction-colimit
clause of the represented-parabolic preservation task.

The concrete direct-sum universal property defines the canonical equivariant
map from the sum of normalized induced representations to normalized induction
of the source sum. Applying the induced projection onto a source summand
recovers that component of the domain. This proves injectivity.

When the actual left quotient `P \ G` is compact, every smooth induced function
has nonzero summand components in one finite set. Choose its uniform open
right stabilizer `K` and a finite double-coset cover `P t K`, supplied by the
published compact-quotient theorem. At each of the finitely many representatives
in `t`, the value in the source direct sum has finite support. Let `S` be the
union of those supports. Projecting to a summand outside `S` gives an induced
function which vanishes at all representatives. Right `K` invariance and
left `P` covariance make it vanish everywhere. The projected component
functions therefore form a finite-support direct-sum vector, whose canonical
image is the original function. This proves surjectivity.

The resulting equivariant linear equivalence identifies the concrete coproduct
cofan of the induced objects with the image of the source coproduct cofan.
Transport of the colimit universal property proves preservation of coproducts.
Both the index universe and the original carrier universe remain explicit;
source carriers are in their maximum and induced carriers are further
saturated by the group universe.

The compactness hypothesis is retained explicitly. This unit neither proves
compactness for an actual represented parabolic nor claims preservation of
coequalizers or all colimits. Those are separate inputs to the unconditional
represented-parabolic target. The construction is derived category
infrastructure based on the published actual function-space induction and
finite double-coset-cover theorem, not a separate translation of Renard.
