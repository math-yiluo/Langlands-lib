# Proof that normalized parabolic restriction preserves finite type

Author: Worker 4814, task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`. Module
`Langlands.Representation.Exponents.LeviJacquetFiniteTypeProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The theorem `leviJacquetFiniteType` proves the published statement
`LeviJacquetFiniteTypeStatement.{u, v}` (module
`Langlands.Representation.Exponents.LeviJacquetFiniteTypeStatement`). This is the
Proposition of Renard 2026, VI.1.3 (printed p.136 / PDF p.142): if a smooth representation
`π` of `G(F)` is finitely generated over `ℂ[G(F)]`, then its normalized Jacquet module
`leviJacquetFunctor … π` is finitely generated over `ℂ[M(F)]`. No hypothesis beyond the
statement's is used. Compactness of the parabolic quotient is imported from its published
proof, not assumed.

## The conditional assembly

`leviJacquetFiniteType_of_quotientCompact` derives `LeviJacquetFiniteTypeStatement.{u, v}`
from `ArbitraryParabolicQuotientCompactStatement.{u}`.

After introducing the field, `G` and `hG`, the proof installs the same instances as the
statement: `hG.isAffineHom` and the topology `RationalPointFamily.pointTopology` on
`rationalPoints G`. It then introduces the two instance hypotheses on `G(F)` and the
parabolic data `p`, `l`, `r`, `hp`, `hl`, `hr`, `hmul`. It installs, as the statement does,
`hl.isConnectedReductive.isAffineHom`, the topology `leviPointTopology l hl` on
`rationalPoints M`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and
`leviPoints_nonarchimedeanGroup p l hp hl`. Finally it introduces `π` and the hypothesis
`hπ` that `π.representation.asModule` is finite over `MonoidAlgebra ℂ (rationalPoints G)`.

1. Compactness: applying the compactness statement to `k`, `G`, `hG`, `P`, `p`, `hp` gives
   `CompactSpace (Induction.LeftQuotient (pointImage p))`.
2. Finite type for the Levi image: the published
   `Langlands.Aubert.General.JacquetFiniteGeneration.finite_of_compactQuotient` (module
   `Langlands.Representation.Aubert.General.JacquetFiniteGeneration`) takes the
   decomposition `isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul` of
   `pointImage p`, the closedness
   `isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup` of the radical
   image, the compact quotient instance, `π` and `hπ`. It gives finiteness of the normalized
   Jacquet module of `π`, a representation of the Levi image `pointImage (l ≫ p)`, over
   `MonoidAlgebra ℂ (pointImage (l ≫ p))`. This is the source's argument: a compact open
   subgroup fixing a generator and the finiteness of `P\G/K` give finitely many generators
   of the Jacquet module.
3. Transport to `M(F)`: by definition `leviJacquetFunctor … π` is that Jacquet module
   pulled back along `e = leviPointsEquiv p l hp hl`, so its representation is the
   composite with `e.toMonoidHom`. The published
   `Langlands.NoetherianRepresentation.finite_comp_surjective_iff` (module
   `Langlands.Representation.Exponents.LeviInductionFiniteTypeReduction`) says that finite
   generation is unchanged by composing with a surjective monoid homomorphism. Applied to
   `e.toMonoidHom` and `e.surjective`, it turns step 2 into the conclusion.

## The theorem

`leviJacquetFiniteType` has type exactly `LeviJacquetFiniteTypeStatement.{u, v}` and takes
no hypotheses. Its proof is `leviJacquetFiniteType_of_quotientCompact` applied to the
published theorem
`Langlands.Aubert.General.RepresentedParabolic.arbitraryParabolicQuotientCompact`, whose
type is `ArbitraryParabolicQuotientCompactStatement.{u}` (module
`Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof`). That theorem
proves compactness of `Induction.LeftQuotient (pointImage p)` for every represented
parabolic `p` of a connected reductive group over a nonarchimedean local field, in the
canonical point topology. So the compactness used in the conditional assembly is proved, not
assumed.

## Relation to `leviJacquetFunctor_obj_finite`

The Library also contains
`Langlands.Aubert.General.RepresentedParabolic.leviJacquetFunctor_obj_finite` (module
`Langlands.Representation.Exponents.LeviCuspidalEmbeddingProof`). Its type is the body of
`LeviJacquetFiniteTypeStatement` written out in full. It is proved there as a step toward
the cuspidal embedding of Renard VI.2.1, by the same three steps, except that compactness
is obtained inline from the dynamic description of parabolics. This module does not import
it. It proves the statement declaration itself, and it depends only on the statement's
module, the compactness theorem and the two finiteness results above, not on the
cuspidal-embedding development.
