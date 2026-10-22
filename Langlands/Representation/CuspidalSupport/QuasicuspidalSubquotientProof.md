# Quasicuspidality and actual smooth Levi subquotients

Authors: Worker 184 and Worker 213.

The closing theorem `Langlands.CuspidalSupport.leviQuasicuspidalSubquotient`
has the existing proposition
`Langlands.CuspidalSupport.LeviQuasicuspidalSubquotientTheorem` as its type.
It covers every prime, actual p-adic field, compatible topological realization,
natural rank (including zero), and block shape. The field and representation
carrier universes are independent. There are no admissibility, irreducibility,
finite-length, or finite-dimensionality hypotheses. The statement module and
its imports are unchanged.

For each proper standard refinement, quasicuspidality means that the actual
coinvariant quotient by the refined unipotent radical is subsingleton.
The proof preserves this condition in three steps.

1. A surjective intertwiner induces a surjection on each subgroup coinvariant
   quotient. Lift a target quotient class to a vector and then lift that vector
   along the intertwiner. Thus quasicuspidality descends along surjective
   intertwiners, in particular the canonical map to an actual invariant-submodule
   quotient. This argument is algebraic and needs no smoothness.
2. For an actual smooth invariant submodule, restrict the canonical injective
   intertwiner to a refined unipotent radical. The ambient representation stays
   smooth because the subgroup inclusion is continuous. The published
   `PadicField.TopologicalData.refinedUnipotent_finite_containment` supplies
   compact open containment of every finite subset of this radical, with the
   prescribed topology. Applying
   `Langlands.coinvariants_map_injective_of_smooth` gives an injective map
   from the subrepresentation's coinvariants to the ambient coinvariants.
   The latter are subsingleton by quasicuspidality, so the former are also
   subsingleton. The containment theorem applies to all ranks and refinements;
   no separate positive-rank reduction is needed here.
3. An actual `SmoothRep.IsSubquotient` witness consists of an invariant
   submodule, its quotient by another invariant submodule, and an isomorphism
   from the specified representation to that quotient. Apply the submodule
   and quotient steps, then the existing invariance of quasicuspidality under
   the equivariant isomorphism obtained from this categorical isomorphism.

Only the injective coinvariant step uses smoothness and compact containment.
The final theorem supplies these inputs from the actual group topology and
smooth representation; it assumes no theorem truth as additional data.
The topology is installed from the supplied `TopologicalData`, with the
published product-Levi topological-group instance.

The quotient step reuses `Langlands.CuspidalSupport.isLeviQuasicuspidal_of_surjective`
from `Langlands.Representation.Filtration.QuasicuspidalVanishingProof`.
The auxiliary results `coinvariants_map_surjective`, `isLeviQuasicuspidal_quotient`,
`isLeviQuasicuspidal_iff_of_iso`, and
`isLeviQuasicuspidal_subrepresentation` expose the individual steps above.
They are internal derivations from the existing actual quotient, inclusion,
and isomorphism constructions and the published exactness and containment
results.

## Provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), section 2.4 opening paragraph, printed page 446 / PDF page 7,
derives subquotient closure from Jacquet exactness in 2.3(a).
Registered source: `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Workers 184 and 213 read this original page on 2026-10-21. The present proof implements
that closure argument on the published product Levis using actual module
coinvariants. It needs injectivity and the elementary quotient-surjectivity
argument, rather than the entire three-term exactness conclusion.

The imported injectivity proof uses compact detection and finite averaging,
as explained in `Jacquet/ExactProof.md`; the imported containment proof uses
finite denominator clearing and finite products, as explained in
`Parabolic/UnipotentFiniteContainment.md`. Their proofs and provenance are
retained in those separate Library modules.
