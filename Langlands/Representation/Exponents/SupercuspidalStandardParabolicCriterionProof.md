# Supercuspidality tested on the proper standard parabolics

Module
`Langlands.Representation.Exponents.SupercuspidalStandardParabolicCriterionProof`.
The theorem
`Langlands.Aubert.General.RepresentedParabolic.supercuspidalStandardParabolicCriterion`
proves exactly the published proposition
`Langlands.Aubert.General.RepresentedParabolic.SupercuspidalStandardParabolicCriterionStatement.{u, v}`.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source assertion is VI.2.1, first block of Remarks, Remark 1
(printed p.137, PDF p.143), read together with the preceding definition:
vanishing of the Jacquet modules along all proper standard parabolics
implies supercuspidality. The standard family is fixed in V.3.8
(printed p.111, PDF p.117); V.3.9 (printed p.112, PDF p.118) supplies
conjugacy of every parabolic to a standard one.

## Exact scope

The field is any nonarchimedean local field `k : Type u` with the
topological and separation instances of the published statement.
`G` is a connected reductive group scheme over `Spec k`; its rational
points have `RationalPointFamily.pointTopology` and the stated local
compactness and nonarchimedean-group instances. A maximal split torus
`i : T.toGrp ⟶ G` and a generic cocharacter `ν` fix the standard family.
The smooth complex representation has arbitrary carrier universe `v`.

The equivalence says that `IsSupercuspidal A` holds if and only if the
normalized Jacquet module vanishes for every proper actual rational
parabolic triple `(p, l, r)` satisfying
`SubgroupFunctor.range p = standardParabolic i ν J` and
`SubgroupFunctor.range (l ≫ p) = standardLevi i ν J` for some
`J ⊆ simpleRelativeRoots i ν`. Properness is `¬ IsIso p`; vanishing is
`Subsingleton` of the underlying Jacquet module. The theorem retains
every hypothesis and both universe parameters of the target.

## Implemented proof

The forward implication applies `IsSupercuspidal A` to the given proper
triple.

For the converse, fix any proper actual rational parabolic triple
`p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`. The proof calls
`parabolicLeviStandardConjugatingPoint` with the proved structural inputs
`parabolicDynamic`, `dynamicGeometricUnipotentRadical`,
`smoothMaximalSplitTorusConjugacy`, and
`relativeRootSystem k G hG T i hi`. It obtains a rational point `g`, an
index `J`, a standard cocharacter, and the two range equalities for
`p ≫ (G.innerIso g).hom` and `l ≫ p ≫ (G.innerIso g).hom`.
The standard-cocharacter property supplies
`J ⊆ simpleRelativeRoots i ν`.

`IsParabolicSubgroup.comp_iso` proves that the conjugated parabolic
inclusion is parabolic. The specified maps `l` and `r` still lie in `P`,
so their rational Levi, geometric unipotent radical, and multiplication
properties apply to this triple. Properness is preserved: an isomorphism
`p ≫ (G.innerIso g).hom`, followed by `(G.innerIso g).inv`, would make
`p` an isomorphism. The assumed standard tests therefore give vanishing
of the conjugated Jacquet module.

The underlying carrier of the normalized Jacquet module is definitionally
`Jacquet.Localization.Coinvariants A.representation (pointImage (r ≫ p)) 1`.
Normalization twists the Levi action and preserves that carrier.
`mem_pointImage_comp_innerIso` identifies the conjugated radical image by
the condition
`x ∈ pointImage (r ≫ p ≫ (G.innerIso g).hom)` if and only if
`g⁻¹ * x * g ∈ pointImage (r ≫ p)`.
`coinvariantsTranslateEquiv` is then a linear equivalence from the
original coinvariants to the conjugated coinvariants, induced by
`[v] ↦ [A.representation g v]`. Its injectivity transfers `Subsingleton`
from the conjugated carrier to the original carrier. Since the original
proper triple was arbitrary, this proves `IsSupercuspidal A`.

The affine structure, canonical rational-point topology, and torus
monomorphism instance are reinstated locally from the statement's data.
All structural results above are imported proved theorems; they add no
premises to the asserted equivalence.
