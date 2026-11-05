# Compactness target for every represented parabolic quotient

`Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement`
is a Prop-valued definition of the quotient compactness input needed by
[ArbitraryParabolicExponentStatement](ArbitraryParabolicExponentStatement.md).
It states a proposition; this module provides no proof of that proposition.

For every universe `u`, it quantifies every `k : Type u` with
`[Field k] [ValuativeRel k] [TopologicalSpace k]`
`[IsNonarchimedeanLocalField k] [T2Space k]`, every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))`, and
`hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and then the
canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`.
Under that topology it retains the host's explicit
`[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]` quantifiers.

For every represented group scheme `P` over the same base, every map
`p : P ⟶ G`, and every `hp : IsParabolicSubgroup p`, the conclusion is exactly

```lean
CompactSpace (Induction.LeftQuotient (pointImage p))
```

Here `pointImage p` is the existing abbreviation from
[ArbitraryParabolic](ArbitraryParabolic.md):
`(rationalPoints.map p).range`. Thus the subgroup is the literal image of
`P(k)` in `G(k)` for the specified map. No choice of a Levi, radical, split
component or representation occurs.

`Induction.LeftQuotient` is the existing carrier from
[LeftQuotient](../../Group/LeftQuotient.md), namely
`Quotient (QuotientGroup.rightRel (pointImage p))`.
Its equivalence classes have the form `P(k) g`, so it represents
`P(k) \ G(k)`. Equivalently, representatives `x` and `y` are related when
`y * x⁻¹ ∈ pointImage p`. Its topology is the canonical quotient topology
of the same `RationalPointFamily.pointTopology` installed above. This is the
published evaluation topology on the affine ambient scheme's rational points.
The declaration introduces no alternative topology or quotient model.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, V.5.1 Corollary, printed page 123 / PDF
page 129. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The corollary asserts compactness of `G/P` for an arbitrary parabolic,
alongside a separate conjugacy assertion. The proposition here isolates its
compactness conclusion in the host's explicit field and ambient group scope;
it includes positive characteristic and does not require a split group.
The retained local compactness, nonarchimedean and Hausdorff hypotheses
express the host's topological setting explicitly.

Renard writes the opposite quotient side. Inversion sends the class
`P(k) g` to `g⁻¹ P(k)` and sends `g P(k)` back to `P(k) g⁻¹`.
The generic published homeomorphism
`Langlands.Induction.quotientInversion` in
[LeftQuotientInversion](../../Group/LeftQuotientInversion.md) implements this
correspondence for the two canonical quotient topologies.
Its theorem `Langlands.Induction.compactSpace_leftQuotient_iff` identifies
their compactness assertions. Continuous inversion is available from the
retained `NonarchimedeanGroup` instance, which extends `IsTopologicalGroup`.
This explains the side convention without adding a premise to the statement.

The source ledger's
[row D07](../../../notes/renard/chapter-v-structural-inputs.md)
keeps the compactness proof as an obligation. The existing helper
`compactSpace_leftQuotient_pointImage_of_dynamic` in
[ArbitraryParabolicFiniteSupportReduction](ArbitraryParabolicFiniteSupportReduction.md)
requires both `GroupScheme.ParabolicDynamicStatement` and
`BruhatTits.DynamicParabolicQuotientCompactStatement`.
Those structural premises are absent from the new proposition. Likewise,
[RationalLeviQuotientCompactness](../Aubert/General/RationalLeviQuotientCompactness.md)
retains ambient quotient compactness or dynamic compactness and does not
prove this target.

The statement adds no standard-cocharacter, dynamic-parabolic,
characteristic-zero, GL, Iwasawa-decomposition or compact-quotient premise.
It asserts no conjugacy, dynamic realization, Iwasawa decomposition, Jacquet
admissibility or finite exponent support. Applying
`finite_normalizedJacquetExponents_of_hasFiniteLength_of_compactQuotient_of_spanning`
from [SplitComponentFiniteSupport](SplitComponentFiniteSupport.md) still
requires proofs of actual quotient compactness and actual Jacquet spanning.
The existing structural programs and their controls remain separate.

Author: Worker 1660.
