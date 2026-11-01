# Representable sheaves on fixed-original-chart domains

This derived construction proves that the quasinet topology of
`OriginalChartDomain a` is subcanonical. It also constructs `domainYoneda`, the
Yoneda functor from these domains to sheaves for that topology. The coefficient
field, ambient point type, and original chart index type have independent
universes `u`, `v`, and `w`.

## Source and scope

The source context is Vladimir G. Berkovich, *Etale cohomology for
non-Archimedean analytic spaces*, Publications mathematiques de l'IHES 78 (1993),
section 1.3, printed page 25 / PDF page 22. The G-topology paragraph describes
coverings by quasinet families of analytic domains and states that representable
presheaves on that domain site are sheaves. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Here the category is the published, restricted `OriginalChartDomain a`: its
objects are actual subsets admitting finite relative neighborhood witnesses
from contained charts of the fixed original atlas, and its arrows are subset
inclusions. The topology is the published `quasinetTopology`, whose
covering sieves satisfy the full finite relative neighborhood condition.
The present proof uses its proved consequence that every target point belongs
to a member of the covering sieve.

This is an internal derivation for that concrete inclusion category. It does
not identify its objects with all analytic domains of the saturated analytic
space. A representable here sends a domain `V` to the type of inclusions
`V ⟶ T` for a fixed domain `T` of the same atlas.

## Implemented proof

`IsCovering.le_of_locally_le` checks a proposed inclusion `S ≤ T` on a covering
sieve of `S`. For each point of `S`, `IsCovering.exists_mem` supplies a sieve
domain `V` containing it. The assumed local inclusion `V ≤ T` puts the point in
`T`, giving the required global subset inclusion.

For `isSheaf_yoneda_obj`, a family of sections of `yoneda.obj T` supplies such
local inclusions. The preceding result constructs `S ≤ T`, and `homOfLE`
constructs its global arrow. All arrows between two fixed objects of the
inclusion category are equal. This proves both that the arrow restricts to
every supplied local section and that any amalgamation equals it. Compatibility
of the local family is automatic by the same thinness, so the proof does not
need the compatibility hypothesis. The argument also includes the empty
domain and its empty covering sieve.

The instance `quasinetTopology_subcanonical` follows from Mathlib's criterion
`GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`.
`domainYoneda` is Mathlib's resulting Yoneda functor into the sheaf category;
its sections lie in `Type v`, the hom universe of Mathlib's category associated
to this order.

## Remaining constructions

This result supplies neither gluing of analytic morphisms into arbitrary
analytic targets nor the structural sheaf of analytic functions. Those involve
bounded algebra maps and their descent, whereas the representables proved to
be sheaves here consist only of inclusions into domains of one fixed atlas.
Atlas saturation, the unrestricted analytic category, and the etale and
equivariant sites remain separate construction obligations.
