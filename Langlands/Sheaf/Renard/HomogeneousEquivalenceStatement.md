# Renard III.3.2: the actual homogeneous category equivalence

These are unproved closed proposition targets for David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, III.3.2, printed p.85 / PDF p.91: the induction-sheaf
identity-coset fibre sentence and the final Theorem identifying induction
and point restriction as mutually inverse functors. The countability
hypothesis is on printed p.84 / PDF p.90. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original pages were read directly.

Both declarations are in `Langlands.Sheaf.Renard.HomogeneousEquivalence`.
They quantify over every actual `G : Type`, topological group structure,
`SigmaCompactSpace G`, explicit `hG : IsLocallyProfinite G`, actual
subgroup `H` and proof of its closedness. Hausdorffness, the compact-open
basis and Renard's countability at infinity are retained. Base, complex
coefficient, section and representation carriers are universe zero,
matching the actual constructions. There is no discrete, open-subgroup,
second-countability or finite-dimensionality restriction.

The sheaf category is the existing `SectionActions.SmoothActionSheaf` on
the original `Langlands.Induction.LeftQuotient H`. Its original action is
`HomogeneousSections.homogeneousAction`: `g₀ • Hg = H(g g₀⁻¹)`. The
representation category is the existing `Langlands.SmoothRep ℂ H`.

`Statement` requires an actual `CategoryTheory.Equivalence` whose forward
functor is exactly `InductionSheaf.functor hG H hH` and whose inverse is
exactly `HomogeneousSections.pointRestriction H hG hH`. Equality of the
functors includes their objects and morphisms. Thus the natural unit,
counit, their invertibility and triangle law must be supplied as
conclusions, not as inputs or unverified certificates.

The first functor reconstructs the actual compact-induced test module by
the smooth equivariant projector-sheaf functor. The second acts on the
literal ordinary stalk at `origin H = H1`, with the original stabilizer
action, and the published proof that the whole stalk is smooth. The
published point-restriction comparison identifies it with the actual
singleton inverse-image restriction followed by compact sections.
No alternative stalk, sheaf, compact-section space or induction model is
substituted.

`OriginStalkStatement` states the preceding fibre assertion as a natural
isomorphism from induction followed by this original-stalk restriction
to the identity on the original smooth H-representation category. It
requires only existence of the natural isomorphism; no particular
evaluation-on-representatives formula is asserted by this target. This is
precisely the source's claim of a natural representation identification.

These propositions are not proofs. The literal compact and smooth-global
alpha and beta comparisons are stated separately in
`HomogeneousSectionStatements`, with their exact inverse formulas and
naturality. The identification of an arbitrary transitive space with the
quotient and the III.3.1 coinvariant statements also remain separate.
