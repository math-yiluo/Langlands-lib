# Positive forms on the literal Levi from its canonical norm kernel

Author: Worker 480. This is a derived supporting construction for the
zero-exponent branch of rational rank-one self-association. It composes
existing actual-object constructions; it makes no new literature claim.

Fix an affine group scheme `G` over an arbitrary nonarchimedean local
field `k`, the displayed torus map `i`, cocharacter `ν`, and finite subset
`I` of the literal `SimpleRoot i ν`. Write `L` for
`Standard.leviScheme i ν (rootSet i ν I)` and `e` for the published
`leviRationalPointHomeomorph i ν I : rationalPoints L ≃ₜ* levi i ν I`.
The ambient point group has exactly `RationalPointFamily.pointTopology`,
the literal Levi has its subgroup topology, and `rationalPoints L` has
exactly `rationalPointTopology`. The independent universes are `u` for
the field and groups and `v` for the representation carrier.

The inputs are local compactness, the nonarchimedean group property and
Hausdorffness of the ambient point group; closedness of the literal
Levi; a central morphism `s : A.toGrp ⟶ L` from a commutative group
scheme; finite index of the actual `splitValuationImage s`; and an
irreducible smooth complex representation `σ` of the literal Levi.
Compact smooth-dual coefficients are assumed on the restriction of
`(SmoothRep.pullbackFunctor e).obj σ` to the actual
`Plancherel.rationalCommonNormKernel L`. This is a condition on every
smooth functional of the restricted action. No admissibility premise
is used.

## The form and the full center

`leviNormKernelPositiveForm` additionally takes a full
`UnitaryCentralCharacter σ.representation`. Its conclusion is an actual
`InvariantPositiveForm σ.representation` on the original carrier and
original literal-Levi action.

Closedness makes the literal Levi locally compact. The homeomorphism
`e` transfers local compactness and Hausdorffness to the canonical Levi
point group. Group operations transfer by its inducing property.
The published `Langlands.subgroupNonarchimedean` and Mathlib's
`NonarchimedeanGroup.nonarchimedean_of_emb`, applied to `e.symm`,
transfer the nonarchimedean property. These facts are proved inside
the module rather than imposed as extra hypotheses about the Levi
scheme.

The pullback has precisely the same carrier, with action
`m ↦ σ.representation (e m)`. Its irreducibility follows from
`Langlands.isIrreducible_comp_continuousMulEquiv_iff`. The published
`UnitaryCentralCharacter.compContinuousMulEquiv` pulls back the full
central character by `Subgroup.centerCongr e.toMulEquiv`. This map
restricts the actual group equivalence to the full abstract centers;
its continuity gives the open kernel, and the original norm-one and
scalar-action laws give the pulled-back laws. No center is replaced
by the image of a torus.

`rationalNormKernelPositiveForm` now constructs a positive form for
this canonical pullback using the supplied compact coefficients and
actual valuation index. That published construction integrates
coefficient products on the full central quotient and proves
definiteness from a nonzero smooth functional and irreducibility.
The present construction retains its entire inner-product core.
For an arbitrary literal Levi element `m`, apply the canonical form's
invariance to `e.symm m`, and cancel `e (e.symm m) = m`. This proves
invariance for the original action, without changing the carrier or
the form. The theorem
`isUnitarizable_levi_of_compact_normKernel_restriction` packages this
form in the existing `IsUnitarizable` predicate.

`leviNormKernelPositiveForm_of_centralTorus` composes this construction
with `leviUnitaryCentralCharacter_of_centralTorus`. Its additional
inputs are the actual structural split-component and compact-center
statements, connected reductivity and the displayed maximal-torus and
genericity hypotheses, and a supplied smooth scalar character of
the full literal center which has unit modulus on
`leviCentralTorusPoints`. The earlier full-center construction proves
unit modulus on the entire abstract center before the new pullback
and coefficient integral are used.

## Dependencies and remaining obligations

The direct mathematical constructions are
`leviRationalPointHomeomorph`, `rationalNormKernelPositiveForm`,
`UnitaryCentralCharacter.compContinuousMulEquiv`,
`isIrreducible_comp_continuousMulEquiv_iff`, and
`leviUnitaryCentralCharacter_of_centralTorus`, together with the stated
topological subgroup and embedding results. The irreducibility
transport uses the order isomorphism on invariant submodules in
`Langlands.CuspidalSupport.isIrreducible_comp_of_surjective`; it does
not use a cuspidal-support theorem. The coefficient-integral
dependencies and the full-center compact-quotient argument are
described in the paired Markdown of `RationalCompactRestrictionUnitarity`
and `RationalLeviFullCenterUnitary`.

These declarations impose no split, quasisplit, characteristic-zero,
or nonempty-root restriction. The main construction does not require
the canonical Levi to be assumed connected reductive. It retains
compact restriction, a central valuation index and the central
character as inputs. The central-torus version additionally retains
its structural premises and the smooth scalar character; it does
not construct that character or prove its torus norm law.
Cuspidality transport is available separately in
`rationalLeviCuspidalityTransport`; deriving compact restriction
from it remains a separate proof obligation.

No Langlands classification, representation-character independence,
geometric lemma or adjointness theorem is used by this construction.
It does not prove `RationalRankOneSelfAssociationStatement`, change
that target, or discharge the missing compactness and index inputs
of its zero-exponent argument.
