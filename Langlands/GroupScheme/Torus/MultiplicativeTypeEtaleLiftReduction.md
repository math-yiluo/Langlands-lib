# Multiplicative-type lifting from smooth subgroup moduli

`recover_subgroup_fibre_inclusion` and `subgroupFibreIso` construct the
actual isomorphism between the fibre source and the given subgroup
source whenever their closed inclusions define the same all-test
subgroup functor. The source group over the neighbourhood need not
descend to the original base. These constructions work for every
scheme `F` with compatible morphisms `b : F ⟶ U` and `c : F ⟶ S`;
there is no field or multiplicative-type hypothesis on this generic
part. `subgroupFibreIso_hom_comp` records the exact raw pullback
inclusion equation for the chosen isomorphism.

`multiplicativeTypeEtaleLift_of_smoothSubgroupModuli.{u}` proves the
unchanged `MultiplicativeTypeEtaleLiftStatement.{u}` under the explicit
hypothesis
`MultiplicativeTypeSubgroupModuli.SmoothMultiplicativeTypeSubgroupRepresentabilityStatement.{u}`.
This is a conditional reduction, not an unconditional proof of the
lifting theorem.

The universal property gives a parameter point over the specified
residue field whose evaluated subgroup functor is the all-test range
of the prescribed inclusion. The published
`Langlands.AlgebraicGeometry.exists_pointed_etale_section` extends this
particular point to a section over a pointed étale neighbourhood.
Pulling the universal inclusion back along that section supplies the
group and its closed inclusion over the neighbourhood. Multiplicative
type and closedness persist under these pullbacks.

The generic composition law for subgroup-family evaluation shows that
the resulting fibre has exactly the original all-test subgroup
functor. Both fibre inclusions are closed immersions and hence
monomorphisms. `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`
therefore gives an isomorphism of their source groups compatible with
their inclusions. Unfolding `Descent.pullbackComparison` gives precisely
the comparison equation in the unchanged target, including its
specified equality transport for the base morphism.

The argument is an internal derived assembly from the cited Library
APIs. The moduli input is the smooth-family consequence of SGA 3,
Exposé XI, Theorem 4.1. The output target is Conrad,
*Reductive group schemes* (2014), Proposition 3.1.6, PDF/printed
pages 83–84. The implemented route uses smooth subgroup moduli;
it does not implement Conrad's Artin approximation proof.
