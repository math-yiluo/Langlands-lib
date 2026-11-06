# Smallness of the actual full-restriction compact induction

Worker 1594. This internal application combines the actual open-subgroup
compact-induction finite-generation theorem, actual finite-generation Hom
coproduct theorem, and actual rational inertia block closure under direct
sums. It supports the smallness component of
`RationalUniversalSmallProgeneratorStatement`; it does not prove that complete
statement.

The field and representation carrier universes `uF` and `uV` are independent.
The group is the actual rational-point group of an affine, locally finite type
group scheme over a nonarchimedean local field, with its canonical topology.
The compact induction uses the entire original representation restricted to
the common kernel of every rational-character norm. Its carrier and the
lifted inertia base have universe `max uF uV`.

`finite_rationalNormKernelCompactInduction_of_finite_restriction` applies
`finite_compactInduced_of_finite` to that actual restriction, using the proved
openness of the common norm kernel. The finite-length variant first uses the
Noetherian consequence of finite composition length, hence finite generation
over the subgroup group algebra. `rationalNormKernelCompactFiniteGenerators`
chooses a finite generating set of the resulting actual ambient group-algebra
module, with its spanning equality.

`rationalInertiaBlockHom_preservesCoproducts_of_finite` specializes
`hom_preservesFullSubcategoryCoproducts` to the actual lifted inertia block.
Its required direct-sum closure is discharged by
`rationalInertiaBlockProperty_directSum`, so no categorical closure or
abelianness premise remains. For each `I : Type (max uF uV)` the conclusion is
preservation of all diagrams of shape `Discrete I` by the actual integer-module
Hom functor.

`rationalNormKernelHom_preservesCoproducts_of_finiteLength` applies that result
to the actual compact induction bundled in the block using any given proof
of membership. Thus its result is exactly the Hom coproduct-preservation
conjunct of the published small-progenerator property for that membership
proof.

The provenance is internal specialization of the three imported constructions.
Finite composition length of the full restriction and block membership are
explicit inputs here. Neither input is claimed as a theorem of this module;
they must be discharged separately when proving the unconditional parent
target. Irreducibility, cuspidality, projectivity, faithful Hom and the other
parts of that target are not established here.
