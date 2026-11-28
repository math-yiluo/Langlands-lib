# Renard VI.3.6, Lemma: realization of an admissible supercuspidal subquotient (proof)

Module
`Langlands.Representation.Exponents.RepresentedSupercuspidalSubquotientRealizationProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

The theorem `representedSupercuspidalSubquotientRealization` proves exactly
`RepresentedSupercuspidalSubquotientRealizationStatement.{u, v}` (module
`Langlands.Representation.Exponents.RepresentedSupercuspidalSubquotientRealizationStatement`).
[Statement](RepresentedSupercuspidalSubquotientRealizationStatement.md)

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.3.6, Lemma, printed pp.147–148 / PDF
pp.153–154, registered as
`renard-2026-representations-groupes-reductifs-padiques`.

## Scope

The theorem has no hypotheses beyond those of the statement. It holds for
every field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
[IsNonarchimedeanLocalField k] [T2Space k]`, every connected reductive group
scheme `G` over `Spec k`, the canonical topology
`RationalPointFamily.pointTopology` on `rationalPoints G` with explicit
`[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]` instances, and all
`π τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with an independent carrier
universe `v`. Given `π.IsAdmissible`, `τ.IsIrreducible`, vanishing of the
normalized `jacquetFunctor` of `τ` for every proper rational parabolic (with
rational Levi, matching geometric unipotent radical and multiplication
isomorphism) and `SmoothRep.IsSubquotient τ π`, it concludes
`SmoothRep.IsSubrepresentation τ π ∧ SmoothRep.IsQuotient τ π`. Its axioms
are `propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

After introducing the telescope, the instance `hG.isAffineHom` and the
canonical topology, the proof is one application of the published reduction
`representedSupercuspidalSubquotientRealizationReduction` (module
`RepresentedSupercuspidalSubquotientRealizationReduction`) to `π` and `τ`.
Besides admissibility of `π`, irreducibility of `τ` and the subquotient
relation, that reduction takes two premises, both supplied here.

1. **Finite index of `⁰G ⊔ Z(G)`.** The premise
   `(Plancherel.rationalCommonNormKernel G ⊔ Subgroup.center (rationalPoints G)).FiniteIndex`
   is `finiteIndex_rationalCommonNormKernel_sup_center` (module
   `RepresentedSupercuspidalCentralProjectivityReduction`) applied to
   `Plancherel.RenardCartan.splitComponentLattice`, the proof of
   `SplitComponentLatticeStatement` (module
   `Langlands.Representation.Plancherel.SplitComponentLatticeProof`).
2. **Compact restriction of `τ` to `⁰G`.** The premise
   `HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup
   (Plancherel.rationalCommonNormKernel G) τ).representation` is
   `representedSupercuspidalCompactRestrictionReduction` (module
   `RepresentedSupercuspidalCompactRestrictionReduction`) applied to `k`, `G`,
   `τ` and the statement's Jacquet-vanishing hypothesis, with its four
   structural premises discharged by their published proofs:
   - `GroupScheme.parabolicDynamic` proves `ParabolicDynamicStatement`
     (module `Langlands.GroupScheme.Absolute.ParabolicDynamicProof`);
   - `GroupScheme.standardCocharacter` proves `StandardCocharacterStatement`
     (module `Langlands.GroupScheme.Rational.StandardCocharacterProof`);
   - `GroupScheme.relativeRootSystem` proves `RelativeRootSystemStatement`
     (module `Langlands.GroupScheme.Rational.RelativeRootSystemProof`);
   - `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` proves
     `JointSpecialCompactBasisExistenceStatement` (module
     `Langlands.BruhatTits.SpecialCompact.JointBasisProof`).

The compact restriction reduction converts the all-parabolic Jacquet
vanishing into cuspidality for the standard parabolics of a maximal split
torus and generic cocharacter, and then derives compact support of the
coefficients on `⁰G` from the special compact subgroup, its simultaneous
standard basis and the Cartan comparison supplied by the joint statement
(Renard VI.2.1 (a) ⇒ (c)). The realization reduction then applies the
generic theorem `Langlands.CuspidalSupport.constituent_of_compactRestriction`
(module `Langlands.Representation.CuspidalSupport.CompactRestrictionRealization`)
to the open normal subgroup `Plancherel.rationalCommonNormOpenSubgroup G`.

## Relation to the source

Renard's proof uses the decomposition of VI.3.5 to place `π` in the block of
`τ`, and then a simultaneous-eigenvalue argument for the free abelian group
`G/⁰G` acting on the finite-dimensional space `Hom_{⁰G}(τ, π)`. The Lean
proof reaches the same conclusion by another route: the generic theorem
`constituent_of_compactRestriction` isolates the finitely many `⁰G`-types of
`τ` by a compact-coefficient isotypic splitting over `⁰G` and replaces the
eigenvalue argument by finite-index constituent induction, which uses the
finite index of `⁰G ⊔ Z(G)`. Its Markdown page describes that route in
detail. The proof uses no source result beyond the published Lean
declarations named above.
