# Determinant-unit reframing of actual admissible Deligne data

This module changes the rational frame of the existing four sheaf data and
constructs a right action of a determinant-unit subgroup on their actual
admissible isomorphism classes. The maps retain the lattice, tangent sheaf and
the map between them. Admissibility of the new representative is proved, and the
quotient relation is preserved by transporting genuine four-data isomorphisms.

The source motivation is V. G. Drinfel'd, *Coverings of p-adic symmetric
regions* (1976), Section 2 A, printed pp.109–110, the four sheaf data and
conditions (a)–(c) defining the points of Deligne's formal scheme. The registered
source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`,
PDF pp.3–4. This module is derived infrastructure for those data:
the source does not separately state this subgroup construction or the
identities proved here.

## Hypotheses and conventions

All carriers have a common universe `u`. The coefficient ring `O` is an arbitrary
commutative ring, `F` is a field with an `O`-algebra structure, and the
four-data objects live on an arbitrary scheme `S` with structural coefficient
map `φ : O →+* Γ(S, ⊤)`. Their dimension parameter `d` is nonzero. The admissible
objects also use `hπ : algebraMap O F π ≠ 0`, as in the existing determinant
condition. The subgroup construction itself does not require nonzero `d` or
`hπ`. There is no extra coefficient-injectivity, flatness, discrete valuation,
local-field or nilpotence hypothesis for these identities.

For a linear automorphism `g` of `F^d`, reframing replaces `r` by `r ∘ g`.
The product of linear automorphisms satisfies `(g * h)(v) = g(h(v))`.
Consequently the implemented formula is

```text
(D.reframe g).reframe h = D.reframe (g * h).
```

This is a right-action convention. The final `MulAction` instance uses the
opposite subgroup to encode this right action as an ordinary left action.

## Actual objects and genuine morphisms

`FramedLatticePiSheaf.reframe_one` and `reframe_mul` prove equality of the actual
framed objects. Their proofs unfold reframing and apply isomorphism
extensionality to the frame. Preservation of identities and composition by the
constant-sheaf functor gives the required frame equalities.

`SheafPreDatum.reframe` changes only the framed eta object. It copies the
underlying lattice, tangent object, total `u`, its homogeneous restrictions,
Pi compatibility, and the local-generation proof. Since all the dependent
domains use the unchanged underlying lattice, these are the original maps.
The identity and product equalities are proved for the complete four-data
structure by congruence and the framed-object equalities.

`FramedLatticePiSheaf.reframeMap` retains the original genuine lattice map.
Its frame square follows by precomposing the original square with the
constant-sheaf image of `g`. `SheafPreDatum.reframeMap` also retains the tangent
map and the original `u` square. The corresponding `reframeFunctor` definitions
prove identity and composition preservation using the existing morphism
extensionality lemmas. `SheafPreDatum.reframeIso` is the actual functorial image
of a genuine isomorphism.

`SheafPreDatum.IsoClass.reframe` is `Quotient.map` on the existing preliminary
isomorphism relation. It is well-defined because `reframeIso` transports
isomorphisms of all four data. Its identity and product laws follow from the
representative equalities by quotient induction.

## Preservation of the three actual conditions

The source's condition (a) concerns the eta lattice on the tangent Pi-zero
loci. Both the lattice and tangent data are unchanged, so
`constantOnPiZeroLoci_reframe_iff` is definitional.

For condition (b), `piQuotientResidueMap_reframe` identifies the actual total
eta-Pi-quotient to tangent-residue-fibre map at every point, by reflexivity.
Thus `residueFibreInjective_reframe_iff` preserves the existing injectivity
condition on that total map.

For condition (c), suppose an actual unit `a : Oˣ` satisfies

```text
LinearMap.det g.toLinearMap = algebraMap O F (a : O).
```

The previously proved
`FramedLatticePiSheaf.normalizedFrameDeterminant_reframe_of_det_unit`
identifies the actual normalized frame determinant at every integer index
and every point. `determinantNormalized_reframe_iff_of_det_unit` rewrites the
right side of the existing determinant condition by these equalities; the
component determinant and the Pi-zero loci are unchanged. In particular it
retains the literal `π^(-n)` scaling after the top exterior power and quantifies
over every `n : ℤ`. Combining the three equivalences proves
`admissible_reframe_iff_of_det_unit`. No new admissibility witness is assumed.

## The subgroup and its action

`determinantUnitSubgroup O d F` is the inverse image under the actual determinant
homomorphism `GL_d(F) → Fˣ` of the image of `Oˣ → Fˣ`. It uses subgroup image
and inverse image, so the identity, product and inverse closure laws are
inherited from genuine group homomorphisms.
`mem_determinantUnitSubgroup_iff` proves that membership is exactly the
displayed determinant equation for some `a : Oˣ`, by extensionality of units.
`SheafPreDatum.admissible_reframe_iff` extracts that witness from subgroup
membership and applies the proved three-condition equivalence.

`SheafDatum.reframe` constructs an admissible representative by this theorem.
Its identity and product equalities follow from those of preliminary data by
subtype extensionality; no equality between chosen proofs is required.
`SheafDatum.IsoClass.reframe` descends this construction through the existing
relation `Nonempty (D.val ≅ E.val)`, using `SheafPreDatum.reframeIso`.

The quotient laws `reframe_one` and `reframe_mul` are proved by quotient
induction from the admissible representative laws. The two cancellation
theorems `reframe_inv_reframe` and `reframe_reframe_inv` then use the subgroup's
group inverse laws. `reframeEquiv` packages these inverse maps as a bijection.
`reframeRightAction` packages identity and product compatibility into
`MulAction (determinantUnitSubgroup O d F)ᵐᵒᵖ` on the actual admissible classes.
`toPreliminary_reframe` proves compatibility with the existing forgetful map
on classes by quotient induction.

## Remaining boundaries

This module proves the action of the specified subgroup on the existing
admissibility predicate. It does not prove the full normalized `PGL(d,F)`
action: general determinants require grading shifts and the resulting central
and coherence laws. Equality of independently constructed exterior subsheaves,
commutation of reframing with arbitrary base change, comparison with the
formal-module moduli problem, and representability remain outside this module.
