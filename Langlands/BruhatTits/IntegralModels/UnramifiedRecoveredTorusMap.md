# Actual torus homomorphisms in recovered apartment models

This internal construction retains the actual supplied lower and upper integral
tori and their generic maps. It works at arbitrary universe and in every field
and residue characteristic.

For `homToSplitTorus`, let R and K be types in the same universe, with R a
commutative domain, K a field, an R-algebra structure on K, and K its fraction
field. Let G be a group scheme over K and D a relative component model over R
for G. Supply commutative group schemes S and S' over K, inclusions i and i'
into G, integral torus data A for S in D, and integral split torus data B for S'
in D.neutral. In addition to A, assume explicitly
`hA : IsSplitTorus A.torus.toGrp`: the structure `IntegralTorusData` alone does
not assert this splitting. For a specified morphism `f : S ⟶ S'`,
`homToSplitTorus` extends f using both supplied generic identifications. Its
generic square reads
`BC(groupHom(homToSplitTorus)) ≫ groupHom(B.genericIso.hom) =
A.genericIso.hom ≫ groupHom(f)`.
The integral inclusion equation additionally assumes the actual factorization
`groupHom(f) ≫ i' = i`. Under that assumption the extension followed by
B.inclusion equals A.inclusion. The proof uses `IntegralTorusHomExtension`
and its generic-fibre rigidity argument.

For `baseChangeTorus`, let F be a valued topological field satisfying
`IsNonarchimedeanLocalField F`, and put K = `inertiaFixedField F`. Supply a group
scheme G over F, lower component-model data D over the valuation integers of F,
upper component-model data E over `fixedFieldIntegers F` for G base changed to
K, and an actual `UnramifiedComponentModelRecovery D E`. Supply integral torus
data A in D and explicitly assume `hA : IsSplitTorus A.torus.toGrp`.
`baseChangeTorus` is the coefficient pullback of A's actual integral torus.
Its inclusion is the pulled-back inclusion followed by the supplied neutral
recovery isomorphism. The generic comparison is the coefficient-square generic
comparison of `A.splitTorusModel hA`. Naturality of model homomorphisms under
coefficient change and the recovery generic square prove the required commuting
square. `baseChangeTorus_isSplit` proves that splitting is preserved by this
base change.

For the apartment specialization, retain this local field F and K. Assume that
G is affine. Supply a commutative group scheme T over F with morphism iT into G
whose coefficient pullback to K is monomorphic on underlying schemes, an actual
`KPApartmentData` D for that upper inclusion and the maximal-unramified integer
valuation, a subset Ω of its apartment, and
`M : RecoveredApartmentFixerModels D Ω`. Also supply a centralizer datum C for
the upper inclusion and the full compatibility proof
`hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C`.
Supply a commutative group scheme S over F, its inclusion iS into G, a proof
`hiS : IsMaximalSplitTorus iS`, and the specified morphism `f : S ⟶ T` with
`hf : groupHom(f) ≫ iT = iS`.
Under these hypotheses `baseChangedLowerApartmentTorus` applies the preceding
construction to M's prescribed lower apartment torus; its integral splitting
is supplied by the recovered-torus API. This lower construction does not
require connected reductivity of G or maximal splitness of the upper torus.

For `apartmentTorusMap` and `apartmentTorusMap_comp_inclusion`, additionally
assume `hG : IsConnectedReductive G` and `hiT`, maximal splitness of the actual
coefficient pullback of iT to K. The map extends the coefficient pullback of the
specified f into M's prescribed upper neutral apartment torus. The inclusion
theorem identifies its composite with the actual upper inclusion with the
pulled-back lower inclusion followed by M's neutral recovery isomorphism.
Its proof applies base-change functoriality to the prescribed factorization hf.
These extra hypotheses and C/hDC are supplied explicitly; they are not fields
of `RecoveredApartmentFixerModels`.

These are derived adapters of the existing torus extension, coefficient
base-change and recovered-torus APIs. They assert no chamber existence, root
survival or equality of an entire neutral integral-point subgroup with a zero
fixer.
