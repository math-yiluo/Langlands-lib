# Reflection along arbitrary surjective étale base change

Author: Worker 693.

This internal helper removes the quasi-compact-cover restrictions from the
property reflection steps needed for arbitrary-base quasi-split descent.
All bases are arbitrary schemes. Every base-change morphism in this module is
étale and surjective; quasi-compactness is not an assumption.

`smooth_of_baseChange_of_etale` and `isAffineHom_of_baseChange_of_etale` reflect
smoothness and relative affineness of a supplied group scheme. They use
published scheme-property descent: fpqc descent implies fppf descent for
target-local properties, and affine morphisms descend under surjective étale
maps.

`IsClosedSubgroup.of_baseChange_of_etale` uses the actual Cartesian square for
the underlying group homomorphism and étale descent of closed immersions.
`isIso_of_baseChange_of_etale` similarly reflects invertibility, first for the
underlying scheme map and then for the group homomorphism.
`isoOfEtaleBaseChange` exposes the resulting actual group-scheme isomorphism;
its homomorphism is the supplied map.

`isCommMonObj_of_baseChange_of_etale` reflects commutativity. Faithfulness of
fppf pullback detects the multiplication equation, and the monoidal comparison
identifies it with the commutativity equation upstairs.

`SubgroupFunctor.le_range_of_etaleBaseChange_le` reflects containment in a
represented subgroup. Pull back any test scheme and use its fppf effective
epimorphic projection. The original point factors through the represented
subgroup if it does so after this projection. The source subgroup functor need
not be representable.

`IsRelativeBorelSubgroup.of_baseChange_of_etale` reflects the relative Borel
property for a supplied closed inclusion in an affine ambient group. Smoothness
descends by fppf reflection; source affineness follows from closedness.
At each base point, a preimage gives a residue-field extension. The field-level
geometric Borel reflection theorem, together with the actual iterated-pullback
comparisons, proves the downstairs geometric Borel condition.
`RelativeBorelData.ofEtaleBaseChange` records this same downstairs presentation
as actual relative Borel data.

`IsReductive.of_baseChange_of_etale` reflects reductivity without an initial
affineness assumption on the group. Relative affineness and smoothness descend.
Each residue-field fibre is connected reductive by field-extension reflection
at a preimage. Extending that fibre to its algebraic closure gives the
pseudo-reductive geometric fibre required by the original relative predicate.

These results reflect properties of supplied objects and maps. They do not
construct effective descent solutions or invariant pinnings.
