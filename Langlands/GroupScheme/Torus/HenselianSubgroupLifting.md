# Lifting prescribed residue torus subgroups over Henselian local rings

This internal construction combines published torus-subgroup representability
with pointed Henselian sections. It supplies the nonsplit residue-torus lifting
step needed in the special-apartment program.

Let `R` be a Henselian local commutative ring, let `k` be a field with an
`R`-algebra structure, and assume `algebraMap R k` is surjective. Write
`c : Spec k ⟶ Spec R` for the induced morphism. Let `G` be a smooth affine
group scheme over `Spec R`. Given an actual closed inclusion
`i₀ : T₀ ⟶ Gₖ`, assume `RelativeTorus.IsTorus T₀`: the source becomes a
finite split torus on an étale cover.

`HenselianTorusLifting.LiftData G i₀` records an actual group scheme `T`
over `Spec R`, a closed inclusion `i : T ⟶ G`, the property
`RelativeTorus.IsTorus T`, and an actual group-scheme isomorphism
`e : Tₖ ≅ T₀` satisfying

```text
baseChange(c, i) = e.hom ≫ i₀.
```

Thus the construction recovers the supplied residue inclusion as an equality of
group-scheme morphisms, with its source isomorphism specified. The selected
definition `HenselianTorusLifting.liftData` chooses such data from the proved
`nonempty_liftData`. It is universe-polymorphic and imposes no characteristic
restriction.

## Implemented proof

The published
`TorusSubgroupModuli.smoothTorusSubgroupRepresentability` gives a smooth
parameter scheme `M` over `Spec R` and an actual universal closed subgroup
`j : K ⟶ G_M`, with `RelativeTorus.IsTorus K`. Its universality is for
the literal subgroup functor on every scheme test. Applying it to
`SubgroupFunctor.range i₀` gives a residue parameter `a : Spec k ⟶ M`
whose evaluated subgroup is that range.

`Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective`
then supplies a section `σ : Spec R ⟶ M` through this exact parameter.
Pulling `K` and `j` back along `σ` gives the integral torus and inclusion;
`baseChangeIdIso` identifies the ambient pullback along the identity with `G`.
Closedness follows from `isClosedSubgroup_familyHom` and composition with this
isomorphism. The relative-torus property follows from its published arbitrary
base-change theorem.

To recover the prescribed fibre, `familyHom_over_identity` identifies family
evaluation over the identity base with ordinary base change of the inclusion.
Its proof uses `Descent.baseChangeIdIso_comparison`. The published
`TorusSubgroupModuli.evaluate_comp` then identifies successive evaluation at
`σ` and `c` with evaluation at `c ≫ σ = a`. The universal-family equality
therefore gives equality of the two actual all-test subgroup ranges.
`IsClosedSubgroup.sourceIsoOfRangeEq` and
`sourceIsoOfRangeEq_hom_comp` turn this equality into the recorded actual source
isomorphism and inclusion square.

## Scope

The input residue torus may be nonsplit, and the ambient special fibre need
not be reductive or connected. This construction asserts neither maximality
of the lift nor containment of any additional supplied integral torus.
It also makes no splitness assertion over a strictly Henselian extension.
Those are further steps toward
`UnramifiedFixedPairSpecialApartmentStatement`; this module does not prove
that statement.
