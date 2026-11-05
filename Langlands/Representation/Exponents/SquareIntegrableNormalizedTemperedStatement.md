# Square-integrable representations are normalized-exponent tempered

Author: Worker 6. Module `Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `SquareIntegrableNormalizedTemperedStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.1, Remark 2, printed p.227 / PDF p.233. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The remark says: if `(π, V)` is irreducible and square-integrable modulo the center, then by Casselman's criterion VII.1.2, `π` is tempered. It refers to the definition of square integrability modulo the center in IV.3.2 (printed pp.99–100 / PDF pp.105–106) and to the definition of temperedness at the start of VII.2.1 on the same page.

This is a **derived** formulation. It drops the irreducibility hypothesis, for the reason explained under "Irreducibility" below.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`. It assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the published temperedness predicate and exponent statements. It then quantifies over

- a measurable structure on `rationalPoints G ⧸ Subgroup.center (rationalPoints G)` that is Borel for the quotient topology, and every Haar measure `haar` on that quotient group;
- every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, with an arbitrary carrier universe `v`.

It asserts that `IsSquareIntegrableModCenter π.representation haar` implies `IsNormalizedExponentTempered hG π`.

## The objects

- `IsSquareIntegrableModCenter π.representation haar` is the published IV.3.2 notion for the abstract center `Subgroup.center (rationalPoints G)`. It consists of three things: admissibility of `π`, a unitary central character `c` (a character of the center with open kernel and modulus one by which the center acts), and, for every smooth-dual functional `λ` and every vector `v`, membership in `L²(haar)` of the absolute coefficient `|φ_{v,λ}|`. That function descends to the quotient because `c` has modulus one.
- `IsNormalizedExponentTempered hG π` is the published derived formulation of the definition in VII.2.1. It consists of admissibility of `π` and, for every actual rational parabolic `p : P ⟶ G`, rational Levi `l : M ⟶ P` and split component `a : A.toGrp ⟶ M`, the condition `SatisfiesNormalizedExponentConeCondition p l a hp hl ha π`. That condition requires a compatible `ParabolicRootPresentation p l a` to exist. It also requires that, for every compatible presentation `pres`, every matching geometric unipotent radical `r` with `IsIso (subgroupMultiplication l r)`, and every normalized Jacquet exponent `χ`, `normalizedRealPart χ` lies in the closed root cone `pres.nonnegCone`. This cone is Renard's `+[𝔞*_M]^G_P`. The real part is the `q^(-s)` parameter of V.3.20. The predicate's own Markdown records the difference between this parameter and the raw-log parameter that V.3.20 also writes. This statement inherits that convention and does not change it.

Every Haar measure on the quotient is allowed. Square integrability does not depend on the choice, but the statement does not use that fact.

## Irreducibility

Renard's IV.3.2 definition (printed p.99 / PDF p.105) asks only that the center act by a unitary character and that every matrix coefficient be in `L²(G, χ, dg*)`. It does not ask for admissibility. Admissibility is needed for Casselman's criterion and is part of the definition of temperedness. Renard obtains it from irreducibility: the Proposition of IV.3.2 (printed p.100 / PDF p.106) shows that an irreducible smooth representation which is essentially square-integrable modulo the center is admissible. The irreducibility hypothesis of Remark 2 serves this purpose.

The published predicate `IsSquareIntegrableModCenter` already contains admissibility and a unitary central character. So the irreducibility hypothesis is not needed, and the statement is made for every representation satisfying the published predicate. An irreducible representation that is square-integrable in Renard's sense satisfies the published predicate, by the IV.3.2 Proposition. That comparison is not formalized here.

## Expected proof route

The remark is a consequence of Casselman's criterion. A proof is expected to proceed as follows.

1. The forward implication of Casselman's criterion applies, because the published predicate gives both of its hypotheses. In the derived form submitted separately as `ArbitraryParabolicCasselmanCriterionStatement`, it puts every `normalizedRealPart χ` in the strictly positive root cone `pres.positiveCone`, for every actual parabolic, presentation, radical and normalized exponent. That statement is not yet in the Library and is not imported here.
2. The published lemma `Langlands.GroupScheme.ParabolicRootPresentation.positiveCone_subset_nonnegCone` gives membership in `pres.nonnegCone`.
3. Admissibility is the first component of `IsSquareIntegrableModCenter`.
4. `SatisfiesNormalizedExponentConeCondition` also requires a compatible presentation for every actual triple `(p, l, a)`. For actual parabolics these come from the choices in V.3.14 (printed p.113 / PDF p.119): a minimal parabolic inside `P` and a maximal split torus containing `A_M`. This existence is a separate structural obligation. It is not proved in the Library, and this module does not assert it.

## Faithfulness notes

- No irreducibility, finite length or finite-dimensionality is assumed. Admissibility and the unitary central character come from the published square-integrability predicate.
- The quotient carries the quotient topology of the canonical topology. Its measurable structure is quantified with `BorelSpace`, and every Haar measure is allowed; their existence is not asserted.
- The local-compactness and nonarchimedean-group instances are standard properties of `G(F)` for a local field. They are quantified, not proved, exactly as in the published temperedness predicate.

## Provenance

This is a derived statement of VII.2.1, Remark 2, for the represented-parabolic interface. It differs from the printed remark in one documented way: irreducibility is omitted because the published square-integrability predicate already contains the admissibility that irreducibility supplies in the source. Temperedness is the published normalized-exponent predicate, with its `q^(-s)` real part and closed root cone. The proof of this statement, the existence of compatible presentations, and the comparison with Renard's IV.3.2 definition remain separate obligations.
