# Cyclic grading shifts of actual Deligne sheaves

This module constructs cyclic degree translations on the actual graded
operator sheaves and flat lattice sheaves used in Deligne's construction.
Translation by `k : ZMod d` makes the new degree `i` the old degree `i+k`.
It retains the total sheaf and its operator, acts on actual homogeneous
morphisms, and is an equivalence with inverse translation by `-k`.

The constructions are derived infrastructure for the four sheaf data in
V. G. Drinfel'd, *Coverings of p-adic symmetric regions* (1976), Section 2 A,
printed pp.109–110 (PDF pp.3–4), registered source
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The precise source inputs are the cyclic grading of `O[Π]`, the graded
lattice `η`, the graded tangent sheaf `T` with invertible components, and
the degree-one Π maps. The source defines `S_i` as the zero locus of the
map from degree `i` to degree `i+1`. It does not separately assert the
functorial translation lemmas proved here.

## Parameters and scope

The generic graded construction uses a category `C : Type u` with morphisms
in `Type u`, a Grothendieck topology `J`, a sheaf `R` of commutative rings,
a compatible section `a`, and `d : ℕ` with `[NeZero d]`. It acts on the
existing `GradedPiSheaf d R a`: the summands are actual module subsheaves
whose sectionwise sum is internal, and the actual operator has `d`-th
power equal to the scalar `a`.

The lattice construction uses an arbitrary commutative ring `O : Type u`,
`π : O`, and topological space `X : TopCat.{u}`. It acts on the existing
`LatticePiSheaf d π X`, whose total sheaf is a sheaf of actual
`PiAlgebra d π` modules, flat on stalks. Its components are sheaves of
`O`-modules with injective inclusions and an internal sum. No nilpotence,
coefficient injectivity, or finite-rank hypothesis is needed for translation.

The line-sheaf and zero-locus specializations use an arbitrary scheme
`S : Scheme.{u}` and a global section `a : Γ(S, ⊤)`. All coefficient and
scheme types use the common universe `u`. The sheaf translation
equivalences apply to the graded categories;
the final bijections apply to the existing quotient of actual line-sheaf
objects by genuine graded isomorphisms.

## Actual graded sheaves

`isInternal_reindex` proves that relabeling an actual internal sum by a
bijection preserves internality. It reindexes independence by the
bijection's injectivity and the supremum by surjectivity, then invokes
Mathlib's criterion for an internal sum.

`GradedPiSheaf.shift` retains the total `PiSheaf`, including its operator
and operator relation. Its component in degree `i` is literally the
original component in degree `i+k`. The degree-one condition follows
from commutativity and associativity in `ZMod d`. `shiftMap` retains the
actual operator-compatible map and reuses its homogeneity in degree `i+k`;
`shiftFunctor` proves identity and composition by extensionality.

`shiftZeroIso`, `shiftAddIso`, and `shiftCancelIso` give genuine
homogeneous isomorphisms

```text
shift 0 M ≅ M
shift l (shift k M) ≅ shift (k+l) M
shift l (shift k M) ≅ M, if k+l=0.
```

Their forward and backward maps are identity maps on the actual total
sheaf. The proofs use the corresponding equalities of component indices.
`shiftNegIso` specializes cancellation to `l=-k`.
`shiftZeroNatIso`, `shiftAddNatIso`, and `shiftCancelNatIso` prove naturality
by extensionality on the total operator sheaf. `shiftEquivalence` takes
shift `-k` as inverse and uses cancellation for its unit and counit.
The triangle law reduces to the identity law on the total sheaf.

## Actual flat lattice sheaves

`LatticePiSheaf.shift` retains the same total coefficient sheaf and the
same stalk-flatness proofs. The degree `i` component and inclusion are
the old ones in degree `i+k`. Its degree-one map is

```text
M.pi (i+k) followed by transport from (i+k)+1 to (i+1)+k.
```

The transport is `eqToHom` of equality of the actual component sheaves.
The inclusion square follows by canceling this index transport and using
the original inclusion square. Thus the operator is still multiplication
by the actual distinguished coefficient Π.

`shiftMap` retains the actual coefficient-linear total map and relabels
its component maps. The comparison isomorphisms have identity total maps
and component maps given by the appropriate index transports.
`component_eqToHom_inclusion` checks those transports against the genuine
inclusions. Their inverse laws and the naturality laws use
`Hom.ext_total`, which determines the component maps through the injective
inclusions. The zero, additive, cancellation and inverse comparisons,
natural isomorphisms, and `shiftEquivalence` parallel the graded
constructions. Their existence is proved without taking comparison
isomorphisms as additional input.

## Fibrewise zero loci and line sheaves

`GradedPiSheaf.componentInclusion_mono` exposes monicity of the genuine
subsheaf inclusion. `shift_componentPi` proves that the shifted
degree-one map, followed by target-index transport, is exactly
`M.componentPi (i+k)`. The proof cancels the monic inclusion and uses the
two actual Π-inclusion equations.

`piZeroLocus_shift` gives the equality of underlying point sets

```text
(M.shift k).piZeroLocus i = M.piZeroLocus (i+k).
```

It pulls the degree-one comparison back along the morphism from the
residue-field spectrum at each point. The target-index transport becomes
an isomorphism under pullback. Composing with that isomorphism preserves
and reflects zero, proving the equality for the existing fibrewise
zero-locus definition. This assertion concerns point sets, not an
independently constructed closed subscheme.

`LinePiSheaf.shift` retains the graded total sheaf and obtains its
local rank-one property from the original component in degree `i+k`.
`LinePiSheaf.IsoClass.shift` descends through the existing genuine
isomorphism relation by applying `GradedPiSheaf.shiftFunctor.mapIso`.
Quotient induction and the actual zero and additive comparison
isomorphisms prove `shift_zero` and `shift_add`. `shiftEquiv` uses shift
`-k` as the inverse bijection on these classes.

## Boundary

The cyclic shift of an unframed lattice does not supply the shifted rational
frame or determinant normalization. This module does not construct a shift of
the full four-data object, preserve its three admissibility conditions, or
construct the full normalized projective action. Exterior-subsheaf comparison,
geometric base-change compatibility of shifts, the formal-module comparison,
and representability remain separate obligations.
