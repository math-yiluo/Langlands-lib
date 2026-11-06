# Reduction of Renard VI.3.6 to compact restriction and finite index

Author: Worker 1498. Module
`Langlands.Representation.Exponents.RepresentedSupercuspidalSubquotientRealizationReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

Source: Renard, *Représentations des groupes réductifs p-adiques* (French
version dated 9 July 2026), VI.3.6, Lemma, printed pp.147–148 / PDF
pp.153–154 (`renard-2026-representations-groupes-reductifs-padiques`).

This is a supporting reduction for the host target
`RepresentedSupercuspidalSubquotientRealizationStatement.{u, v}`. It is not a
proof of that target. The module defines the proposition
`RepresentedSupercuspidalSubquotientRealizationReductionStatement.{u, v}` and
proves it as `representedSupercuspidalSubquotientRealizationReduction`.

## Statement

The proposition quantifies over the same telescope as the published target:

- a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local
  field of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`;
- the instance `hG.isAffineHom`;
- the canonical topology `RationalPointFamily.pointTopology` on
  `rationalPoints G`, with `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]`;
- `π τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)`. The carrier universe `v`
  is independent of `u`.

The target's all-actual-parabolic Jacquet-vanishing hypothesis is replaced
by two explicit premises:

1. `(Plancherel.rationalCommonNormKernel G ⊔ Subgroup.center (rationalPoints
   G)).FiniteIndex`. This is the finiteness of `G/⁰G Z(G)` that Renard uses
   in VI.3.2.
2. `HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup
   (Plancherel.rationalCommonNormKernel G) τ).representation`. This is
   Renard VI.2.1(c) for `τ`: its restriction to the common norm kernel `⁰G`
   is compact. Every coefficient against a smooth functional of the
   restricted action has compact support on `⁰G`.

Under these premises, together with `π.IsAdmissible`, `τ.IsIrreducible` and
`SmoothRep.IsSubquotient τ π`, the proposition concludes
`SmoothRep.IsSubrepresentation τ π ∧ SmoothRep.IsQuotient τ π`. So `τ` embeds
into `π` by an injective intertwiner and is a quotient of `π` by a surjective
one. The two maps are not claimed to split each other.

Neither premise is proved here.

- Premise 2 follows from the target's Jacquet vanishing by Renard VI.2.1
  (a) ⇒ (c). Worker 1595's conditional supporting candidate
  `RepresentedSupercuspidalCompactRestrictionReductionStatement` derives it
  from four structural statements.
- Premise 1 is a structural property of connected reductive groups. Its proof
  belongs to the split-component lattice owners.

Once both are available, the target follows by instantiating this reduction.

## Implemented proof

The proof installs four things:

- The affine instance, from `isAffine_of_isAffineHom`.
- Smoothness of `G`, from `hG.smooth`. It supplies the local finite type
  needed by the norm-kernel topology lemmas.
- Hausdorffness of the rational points
  (`Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space`).
- The norm kernel as the open subgroup
  `Plancherel.rationalCommonNormOpenSubgroup G` (openness from the published
  `isOpen_rationalCommonNormKernel`), with its published normality instance
  `rationalCommonNormKernel_normal`.

It then applies the generic theorem
`Langlands.CuspidalSupport.constituent_of_compactRestriction` from the
ancillary module `Langlands.Representation.CuspidalSupport.CompactRestrictionRealization`,
submitted with this pair, with `H = ⁰G`. That module's Markdown describes the
generic argument and how it relates to Renard's proof.

## Provenance

This proposition is derived and internal. It isolates exactly the two inputs
that the implemented route to VI.3.6 needs, keeping the rest of the target's
telescope and its conclusion unchanged.
