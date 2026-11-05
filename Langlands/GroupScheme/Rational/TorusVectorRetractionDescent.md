# Unique torus-valued maps and descent of central-torus retractions

This is internal derived work using the split retraction in
`TorusVectorExtensionSplit`, finite Galois splitting of tori, the actual finite
Galois tensor decomposition, and fpqc descent of compatible homomorphisms.
It supplies the nonsplit retraction needed for rational-point factorization.

For a field `k : Type u`, let `z : Z ⟶ E` be a closed central torus inclusion
in a group scheme affine over `k`, and let `p : E ⟶ Q` be an actual fppf
quotient with kernel `range z`. If `Q` has natural vector coordinates of
finite dimension `n`, `exists_retraction_of_vector_quotient` constructs
`r : E ⟶ Z` with `z ≫ r = 𝟙 Z`.
`retractionOfVectorQuotient` chooses such a map and
`comp_retractionOfVectorQuotient` records its identity. There is no assumption
on the characteristic, perfection of `k`, or commutativity of `E`.
The vector-group and central-kernel hypotheses are explicit.

The intermediate `hom_ext_of_unipotent_quotient` says that torus-valued maps
are determined on the specified kernel of an affine unipotent quotient.
Here the inclusion is a monomorphism, and the fppf projection is explicitly
quasi-compact, so fpqc quotient descent applies. The difference of two maps
is an actual group homomorphism because the target torus is commutative.
The kernel identification shows that this difference kills the full scheme
kernel. Descending it through the projection and using the theorem that maps
from affine unipotent groups to arbitrary tori are trivial proves equality.

`unipotent_baseChange` and `torus_baseChange` apply the field-extension
results to arbitrary morphisms of field spectra by recovering their algebra
structures. `compatible_retraction_onFieldComponents` handles a descent datum
over a field whose double overlap is isomorphic to a finite coproduct of
field spectra. On each component, the two candidate descended retractions
agree on the pulled-back kernel: compatibility of the inclusion and the
retraction identities give that agreement. The preceding uniqueness theorem
then equates the two maps. Finite-component detection yields the compatibility
square on the whole overlap. Its hypotheses require affine source and
quotient over the field and unipotence of the quotient.

For the main retraction theorem, split `Z` over a finite Galois extension
`L / k`. The vector coordinates remain vector coordinates over `L`, giving
affineness and unipotence of the quotient there. Closedness, centrality and
the actual fppf kernel identity all survive base change. The split retraction
therefore exists over `L`. The canonical descent data and the proved finite
Galois field components meet the compatibility theorem's hypotheses. Fpqc
homomorphism descent gives `r` over `k`; faithful base change reflects its
retraction identity.

This unit constructs the retraction only. A complementary quotient section
and the final positive-power rational-point factorization remain separate
steps of the host proof.
