# Existence of the cocenter quotient and its cocharacter properties

Authors: Workers 1616 and 1435.

`Langlands.GroupScheme.cocenterQuotientExistence` proves exactly
`Langlands.GroupScheme.CocenterQuotientExistenceStatement.{u}`.
For every field `k : Type u`, connected reductive group scheme `M` over
`k`, and actual derived subgroup `d : D ⟶ M`, it supplies a commutative
group scheme `Q` and a homomorphism `q : M ⟶ Q.toGrp`. The underlying
scheme of `Q` is affine, `q` is an fppf quotient with full kernel
`SubgroupFunctor.range d`, and `Q.toGrp` is a torus.

For every supplied maximal torus `t : T.toGrp ⟶ M` and every field
extension `E : Type u` of `k` splitting `T`, the theorem also supplies
splitness of `Q_E` and surjectivity of the integral cocharacter map
`ν ↦ ν ≫ (Additive.ofMul (t ≫ q))_E`. These conclusions use the exact
base-change functors and cocharacter lattices in the public statement.
The universe `u` is arbitrary. There is no restriction on characteristic
or perfectness, and no additional affineness hypothesis on `T`.

The implemented proof applies
`cocenterQuotientExistence_of_product_of_torus_intersections` to the two
proved Library theorems `derivedMaximalTorusProductSurjectivity` and
`derivedMaximalTorusIntersection`. The former proves scheme surjectivity
of multiplication of the actual derived subgroup and each specified
maximal torus. The latter proves that their full scheme-theoretic
intersection is a torus over the original field. Its type unfolds to
exactly the second input of the assembly theorem, so both structural
inputs are discharged without further hypotheses.

The assembly first uses `cocenterTorusQuotientData` to choose a smooth
affine commutative fppf quotient by the actual derived subgroup.
Product surjectivity makes every `t ≫ q` scheme-surjective.
The split-image construction shows that `Q` splits over every field
splitting `T`; maximal-torus existence then supplies a splitting field
that witnesses the torus property of `Q`.

For the integral conclusion, the assembly identifies the full kernel
of the base-changed restricted quotient with the base change of the
actual intersection. The intersection theorem therefore makes that
kernel a torus, hence smooth and connected. The assembly obtains an
epimorphism of the split tori and applies
`IsSplitTorus.cocharacter_surjective_of_smooth_connected_kernel`.
Thus the conclusion is surjectivity on the integral lattice itself.

This is an internal composition of the named Library results. Its
mathematical provenance is the derived cocenter formulation explained in
`CocenterQuotientStatement.md`; this proof uses the implemented quotient,
product, full-intersection and cocharacter constructions. The new
module adds only the exact unconditional theorem.
