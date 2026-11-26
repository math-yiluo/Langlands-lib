# Chevalley groups over the integers: proof of splitness and classification by one fibre

`Langlands.GroupScheme.chevalleyGroupClassification` proves exactly
[`ChevalleyGroupClassificationStatement.{u}`](ChevalleyGroupClassificationStatement.md)
in every universe `u`, with no added hypotheses. Throughout, `ℤ` is `ULift.{u} ℤ` and
`Spec ℤ` is `Spec (CommRingCat.of (ULift.{u} ℤ))`, as in the statement.

The module adds two local instances, `IsDomain (ULift.{u} ℤ)` and
`IsPrincipalIdealRing (ULift.{u} ℤ)`, both transported from `ℤ` along
`ULift.ringEquiv`, and two theorems. It adds no axiom.

## Clause 1: `integerReductive_split`

`integerReductive_split` takes a reductive `G` over `Spec ℤ`, a commutative group
scheme `T` over `Spec ℤ` with `RelativeTorus.IsTorus T.toGrp`, and `t : T.toGrp ⟶ G`
with `IsFibrewiseMaximalTorus t`. It returns exactly the conclusion of clause 1 of the
statement. It does not use the hypothesis `IsClosedSubgroup t`, so the theorem omits it.

1. `integerTorusSplit` (every torus over `Spec ℤ` is split, Conrad Corollary B.3.6)
   gives a finite type `I` and an isomorphism `e : T.toGrp ≅ splitTorus (Spec ℤ) I`.
2. `IsFibrewiseMaximalTorus.iso_comp`, applied to `e.symm`, transports fibrewise
   maximality from `t` to the coordinate torus `e.inv ≫ t : splitTorus (Spec ℤ) I ⟶ G`.
3. `exists_fibrewiseRootDatum_of_isDomain` (over any commutative domain, here `ℤ`) gives
   a root datum `P` on `I → ℤ` with `IsFibrewiseRootDatumOf I G (e.inv ≫ t) P`. This is
   the constancy of roots and coroots over the connected base (the remark after Conrad's
   Definition 5.1.1).
4. `pidRootWeightSpace_nonempty_linearEquiv` (over any principal ideal domain, here `ℤ`)
   gives, for every root `α`, a linear isomorphism from
   `splitTorus.exponentWeightSpace I G (e.inv ≫ t) (P.root α)` onto `ℤ`. This is the
   triviality of the root line bundles on `Spec ℤ`.

The isomorphism returned for the statement is `e.symm : splitTorus (Spec ℤ) I ≅ T.toGrp`,
whose `hom` is `e.inv`, so the coordinate torus of the statement is `e.inv ≫ t`.

The lemma of step 4 and the statement use different module structures on the source
weight space `W = splitTorus.exponentWeightSpace I G (e.inv ≫ t) (P.root α)`. The lemma
is stated over a general ring, so on `W` it uses the submodule structure
`Submodule.module`. In clause 1 of the statement, over the ring `ULift ℤ`, instance
search instead gives `W` the structure `ULift.module`, obtained from the module
structure `AddCommGroup.toIntModule` of the additive group `W` over the unlifted
integers. Both use the module structure of the target `ULift ℤ` over itself. The
proof forgets the isomorphism of step 4 to an additive
equivalence, naming the submodule structure on `W` explicitly. It then rebuilds the
additive equivalence as a linear isomorphism for `ULift.module` on `W` with
`Langlands.LinearAlgebra.liftedIntLinearEquivOfAddEquiv`. That definition makes any
additive equivalence between `ULift ℤ`-modules linear, for any module structures,
because scalar multiplication by `ULift ℤ` is integer multiplication.

## Clause 2: `chevalleyGroupClassification`

The first component of the theorem is `integerReductive_split`. For the second, take
Chevalley groups `G` with `t : T ⟶ G` and `H` with `t' : T' ⟶ H`, and a field `k` with
an algebra structure over `ℤ`. Applying `integerReductive_split` to both gives coordinate
split tori `i = e.hom ≫ t` and `j = e'.hom ≫ t'`, root data `P` and `Q`, and free
rank-one root spaces. `IsFibrewiseMaximalTorus.iso_comp` and `IsClosedSubgroup.iso_comp`
transport fibrewise maximality and closedness to `i` and `j`.

- From `G ≅ H` to `G_k ≅ H_k`: the base-change functor along `algebraBaseMap ℤ k` maps
  the isomorphism.
- From `f : G_k ≅ H_k` to `G ≅ H`:
  1. `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise` shows that the base changes
     of `i` and `j` are maximal tori of `G_k` and `H_k`, and `IsFibrewiseRootDatumOf.field`
     shows that `P` and `Q` are their root data.
  2. `nonempty_rootDatumEquiv_of_iso` (over any field: pass to an algebraic closure and
     conjugate the maximal tori) gives an equivalence of these realized root data from
     `f`, and `CoordinateRootDatum.equivOfFieldRealizationEquiv` turns it into an
     equivalence `P ≃ Q` of the coordinate root data.
  3. `affineSplitIsomorphismTheorem` with `R = ULift ℤ` (Conrad Theorem 6.1.17 over an
     affine base), applied to the inverse equivalence `Q ≃ P` and the split structures of
     `G` and `H`, gives an isomorphism `G ≅ H`. The root-space hypotheses of that theorem
     come from the rank-one root spaces of clause 1, with the conversion of clause 1
     reversed. Each isomorphism is forgotten to an additive equivalence, naming
     `ULift.module` on the source weight space explicitly. It is then rebuilt with
     `liftedIntLinearEquivOfAddEquiv` for the submodule structure `Submodule.module`
     that the general affine theorem uses on that weight space.

The proof follows Conrad, *Reductive group schemes* (2014), p.230: the paragraph before
Proposition 6.4.1 for clause 1 and the proof of Proposition 6.4.1 for clause 2. The
field comparison extends the final assertion of Proposition 6.4.1 from the complex
fibre to an arbitrary field fibre.
