# Canonical scalars on original nondegenerate Hom spaces

This module constructs the scalar structure on the original additive Hom spaces
and the unitized Hom comparison in David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, I.2.1, printed page 14 /
PDF page 20. Worker 6 authored this Lean/Markdown pair; Worker 751, the focused
executor, audited it against the source, added further interface checks and
submits it. All declarations below are in
`Langlands.Algebra.NondegenerateModuleHomScalars`.

The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The conventions on printed pages 5–6 / PDF11–12 allow associative rings without
a unit and additive modules without a unit law. I.1.2, printed page 7 / PDF13,
defines nondegeneracy by fixing idempotents. I.2.1 first constructs canonical
complex scalars and proves automatic linearity, then gives the Hom scalar
formula and the Hom equality in (I.2.1.2). These passages were read directly;
I.2.2 / PDF21 was also read to locate the later functor and exactness assertions.
No Renard errata note was present in the current project notes tree.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, was read directly. It requires a separately supplied complex vector
space for the old printed-page-314 theorem about arbitrary nonunital modules.
Here the scalar structures are recovered from nondegeneracy, as specified by
the governing 2026 passage. No prior scalar module on the carriers or assumed
linearity of their original intertwiners is an input to this construction.

The source setting is `ℂ`. The general construction here uses a commutative
ring `k`, which is an internal generalization compatible with the existing
unitization interface. It uses no scalar inverses, cardinal or dimension
bounds. The named structures, linear inclusions and equivalences, entire-map
interfaces and composition laws are internal packaging of the source formulas,
with their intrinsic proofs described below. The exact complex specialization
is provided explicitly.

## Original structures and pointwise scalars

The scalar ring, algebra and carriers have independent universes `uK`, `uA`,
`uM`, `uN` and `uP`. The inputs include the original `NonUnitalRing A`,
`Module k A`, `IsScalarTower k A A` and `SMulCommClass k A A`; the last two
assumptions retain bilinearity of the algebra multiplication. Each carrier has
its specified `AddCommGroup` and original `NonUnitalModule A` action.
`hA : IsIdempotented A` and the nondegeneracy proofs are explicit propositions.
There is no unit or commutativity assumption on `A`, and no nontriviality or
finiteness assumption. Every recovered scalar structure is exactly the
published `NondegenerateScalars.module k hA hM`, installed locally.

`scalarMul k hA hN c f` is an element of the original
`NonUnitalModuleHom A M N`, with additive map `c • f.toAddMonoidHom` in the
recovered scalar structure on `N`. Its intertwining law follows by applying
the original intertwining equation for `f` and the published commuting scalar
adapter on `N`. `homModule k hA hN` gives this original Hom carrier a named
`Module k` structure, retaining exactly the pointwise additive group from
`NonUnitalModuleAdditive`. All module laws are proved by original-Hom
extensionality and the corresponding laws on `N`.

This construction needs only target nondegeneracy: the source can still be any
original additive module. That is a stronger internal version of the source
construction on two nondegenerate modules. The comparisons with scalar-linear
maps use both nondegeneracy proofs. No global scalar instance is introduced.

`scalarMul_apply` and `smul_apply` expose pointwise target scaling.
`smul_toAddMonoidHom` identifies the whole additive map, and `smul_function`
identifies the entire underlying function. `smul_apply_eq_source` gives the
other source formula, `(c • f)(m) = f(c • m)`, by the already published automatic
linearity theorem `NondegenerateScalars.map_smul`.

## Linear maps and the existing intertwiner submodule

`toLinearMap k hA hM hN` is the actual linear inclusion from the original Hom
scalar module into `M →ₗ[k] N`, with both carrier scalar modules recovered.
Its values are exactly the published `NondegenerateScalars.toLinearMap`.
Original Hom addition and the new scalar action are pointwise, so linearity
follows by linear-map extensionality and reflexivity. The application,
`toLinearMap_toAddMonoidHom` and `toLinearMap_function` interfaces retain the
original value, entire additive map and entire function. Injectivity follows
by evaluating an equality of linear maps at every vector and applying original
Hom extensionality.

`intertwinersEquiv` is a linear equivalence onto exactly the published
`CompatibleUnitization.intertwiners` submodule, with action homomorphisms
`NondegenerateScalars.toLinearEndHom` on the two recovered modules. Its forward
map is the above inclusion together with the original intertwining equation.
Its inverse takes the underlying additive map of an element of that submodule;
submodule membership is precisely the original intertwining law. The inverse
identities follow by Hom, subtype and linear-map extensionality. The additive
and scalar laws are definitional equalities for these actual pointwise
structures. No new carrier of intertwiners is introduced. This submodule is the
Lean form of the intersection `Hom_A(X,Y) ∩ Hom_ℂ(X,Y)` displayed in I.2.1
just before (I.2.1.2).

The `intertwinersEquiv_apply`, `symm_apply`, `toAddMonoidHom`,
`symm_toAddMonoidHom`, `function` and `symm_function` declarations expose both
directions at a point and as full maps. `intertwinersEquiv_left_inv` and
`right_inv` expose both inverse identities.

`toLinearMap_id`, `toLinearMap_comp`, `intertwinersEquiv_id` and
`intertwinersEquiv_comp` retain original identity and composition as equalities
of complete maps. `comp_smul` uses automatic scalar linearity of the outer
original intertwiner. `smul_comp` is the pointwise equality for precomposition.
Together with the already published additive composition laws, these give
bilinearity of original Hom composition.

## Actual unitized modules and Hom comparison

`unitizedModule k hA hM` specializes the published
`CompatibleUnitization.module` to the recovered action homomorphism. It is the
actual unital `Module (Unitization k A) M`, installed only locally.
`unitized_smul` and `unitized_smul_function` give
`x • m = x.fst • m + x.snd • m`, where the scalar-coordinate action is recovered
and the `A` action is original. `unitized_inr_smul` and `unitized_inl_smul`
expose restriction to `A` and the scalar coordinate. Their proofs specialize
the published unitization laws. `unitizedSmulCommClass` specializes the
published commuting adapter used by the `k`-module of unitized linear maps.

`unitizedHomEquiv` is the composite of `intertwinersEquiv` with the inverse of
`CompatibleUnitization.linearMapEquiv` for these recovered action
homomorphisms. It is an actual `k`-linear equivalence from the original additive
Hom carrier to `M →ₗ[Unitization k A] N`, with all structures chosen explicitly.
This expresses the Hom equality in (I.2.1.2) using the existing Lean carriers.
Its construction uses the existing unitization comparison and assumes no new
comparison property.

The forward and inverse application, additive-map and function identities show
that it retains the complete original maps in both directions. The two inverse
identities specialize the corresponding linear-equivalence laws.
`unitizedHomEquiv_id`, `comp`, `symm_id` and `symm_comp` retain identity and
composition as whole maps in both directions; these are definitional
equalities of the existing constructions.

`complexHomModule` and `complexUnitizedHomEquiv` are the exact complex case.
The algebra and carrier universes remain arbitrary and independent. Their
carrier scalar modules are the published `NondegenerateScalars.complexModule`.

## Interface and zero-case checks

Complete unapplied assignments check the principal constructors, linear maps,
equivalences, underlying additive maps and whole-function identities at
arbitrary independent universes. At arbitrary universes they also cover the
source formula `smul_apply_eq_source`, injectivity of the linear inclusion, the
restriction and scalar-coordinate interfaces of the unitized module,
`intertwinersEquiv_comp` and `unitizedHomEquiv_symm_comp`. The main assignments
are checked separately
at `(uK,uA,uM,uN,uP) = (0,1,0,1,0)` and `(1,0,1,0,1)`, including the composition
and scalar composition laws. Full complex constructors are also checked.
These assignments include the whole telescope, so they check the absence of a
hidden prior scalar module or supplied intertwiner-linearity premise.

Further checks explicitly select the original ambient ring, source and target
additive groups and original algebra actions when competing structures coexist.
They also select the named recovered carrier scalar modules, Hom scalar module
and unitized modules in the presence of competing scalar and unitized module
instances. The complete scalar function, linear inclusion, intertwiner
comparison and unitized comparison retain those choices. The overlapping-instance
linter is disabled only in sections intentionally installing duplicate ambient,
additive-group or original-action instances.

For a subsingleton target, original Hom extensionality shows the Hom carrier is
subsingleton and its scaled maps vanish. For a subsingleton scalar ring, the
constructed Hom module and `1 = 0` force every Hom element to vanish. For a
subsingleton ambient algebra, the nondegeneracy fixer equation and the original
zero-action law force every vector to be zero; the unitized comparison then
vanishes pointwise. A subsingleton source also makes the forward unitized map
zero, using additivity at zero. None of these cases is excluded by a
nontriviality assumption.

The tensor construction and tensor equality in (I.2.1.2), Hom/tensor functors,
exactness, associativity, category equivalences, new endomorphism algebra
structures and center classifications remain separate obligations. This pair
claims only the constructions and intrinsic laws described here. Development
compilation is separate from independent semantic acceptance and publication.
