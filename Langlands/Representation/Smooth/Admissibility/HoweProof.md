# Howe's finite-length implication on actual reductive rational points: proof

The module `Langlands.Representation.Smooth.Admissibility.HoweProof` proves
`Langlands.SmoothRep.rationalPointsFinitelyGeneratedAdmissibleFiniteLength`, whose
type is exactly
`Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, uV}`
from `Langlands.Representation.Smooth.Admissibility.HoweStatement`.

## What is proved

This is the finite-type-and-admissible implication of Renard VI.6.3 (David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026,
printed pp. 178–179 / PDF pp. 184–185). For every nonarchimedean local field
`F : Type u`, of characteristic zero or positive characteristic, every connected
reductive group scheme `G` over `F`, and every smooth complex representation
`A : SmoothRep.{0, u, uV} ℂ (RationalPoint F G.X)` of the rational points with the
canonical rational-point topology `rationalPointTopology F G.X`: if
`A.representation.asModule` is a finitely generated module over the group algebra
`MonoidAlgebra ℂ (RationalPoint F G.X)` and `A` is admissible, then `A` has finite
length over that group algebra. The field universe `u` and the carrier universe `uV`
are independent, and the zero representation is included. Finite generation is over
the group algebra, not finite dimension over `ℂ`. The theorem has no hypotheses
beyond those of the statement.

## The proof

The proof is a single application of the rational Howe assembly
`Langlands.SmoothRep.rationalHoweJointAssembly`, instantiated at universes `u` and
`uV`. That theorem proves `RationalHoweJointAssemblyStatement.{u, uV}`: six
structural and representation-theoretic results together imply the target. Each is
supplied by a theorem of the Library:

1. `Langlands.GroupScheme.standardCocharacter` proves
   `StandardCocharacterStatement.{u}`: existence of standard cocharacters and
   agreement of the standard parabolic, Levi and unipotent subgroup functors with
   their dynamic subgroups.
2. `Langlands.GroupScheme.standardLeviIntersection` proves
   `StandardLeviIntersectionStatement.{u}`: the semidirect decomposition of nested
   Levi–parabolic intersections and the rational unipotent product.
3. `Langlands.GroupScheme.relativeRootSystem` proves
   `RelativeRootSystemStatement.{u}`: the relative roots of a maximal split torus
   form a root system whose Weyl group is the image of `N(k)/Z(k)`.
4. `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` proves
   `JointSpecialCompactBasisExistenceStatement.{u}` (Renard V.5.1–V.5.2): one special
   compact subgroup `K0` at a special vertex, with its Iwasawa products, its Cartan
   comparison and a simultaneous basis of compact open subgroups normal in `K0`,
   each with the ordered-intersection (Iwahori) and contraction properties for every
   standard parabolic (`SimultaneousStandardBasisAt`).
5. `Langlands.Aubert.General.rationalCuspidalCompactRestriction` proves
   `RationalCuspidalCompactRestrictionStatement.{u, max (u + 1) uV}` (Renard VI.2.1,
   (a) implies (c)): for a cuspidal representation, the restriction to the common
   rational-character norm kernel `Plancherel.rationalCommonNormKernel G` has
   compactly supported matrix coefficients on that subgroup, with its subspace
   topology, against every smooth vector of the dual of the restriction
   (`HasCompactSmoothDualCoefficients` of `SmoothRep.restrictSubgroup`). The
   compactness is on the norm kernel itself; it is not compact support of the
   coefficients on the whole group modulo the norm kernel.
6. `Langlands.CuspidalSupport.rationalNormKernelFiniteRestriction` proves
   `RationalNormKernelFiniteRestrictionStatement.{u, max (u + 1) uV}` (Renard
   VI.3.2(ii)): the restriction of an irreducible representation to the common
   rational-character norm kernel is semisimple of finite length and is spanned by
   finitely many irreducible subrepresentations.

The last two results are universe-polymorphic in the carrier universe and are used
at `max (u + 1) uV`, the universe to which the assembly lifts the representation.

Inside the assembly, the representation is lifted to the larger carrier universe,
a single compact open subgroup `K` of the joint basis, normal in `K0`, is chosen
fixing a finite generating family, and every irreducible subquotient is shown to
have a nonzero `K`-fixed vector through a cuspidal constituent of one of its
normalized Jacquet modules. The compact-open detection criterion then gives finite
length. This route differs from the proof printed in Renard VI.6.3, which bounds
the length by `dim V^K` using the preceding lemma, proposition and corollary of
VI.6.3; the module proves the finite-length conclusion only.

## Scope

The module proves the finite-type-and-admissible implication and nothing else. The
converse implication is the separate statement
`Langlands.Aubert.General.RationalPointsFiniteLengthAdmissibleStatement`, which is
neither used nor proved here. The bound of the length by the dimension of the
fixed vectors of a compact open subgroup, and the intermediate lemma, proposition
and corollary of Renard VI.6.3, are not stated or proved in this module.
