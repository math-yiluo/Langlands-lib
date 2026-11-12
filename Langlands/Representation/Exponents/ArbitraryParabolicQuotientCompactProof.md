# Compactness of the literal rational-point quotient for every represented parabolic

`Langlands.Aubert.General.RepresentedParabolic.arbitraryParabolicQuotientCompact`
proves the unchanged published proposition
`Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u}`
of [ArbitraryParabolicQuotientCompactStatement](ArbitraryParabolicQuotientCompactStatement.md)
at its universe `u`. The theorem has no hypotheses. Its type is exactly the
proposition, so it covers every field and group that the proposition quantifies.

## What is proved

Take any `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k]`
`[IsNonarchimedeanLocalField k] [T2Space k]`. Take any group scheme
`G` over `Spec (CommRingCat.of k)` with `hG : IsConnectedReductive G`. Put the
canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`,
as the statement does. For every local-compactness and nonarchimedean-group
instance on that space, every represented `P`, every `p : P ⟶ G` and every
`hp : IsParabolicSubgroup p`, the theorem proves

```lean
CompactSpace (Induction.LeftQuotient (pointImage p))
```

Here `pointImage p` is the literal range of `rationalPoints.map p`.
`Induction.LeftQuotient` is the existing quotient by `QuotientGroup.rightRel`,
with classes `P(k) g`, in its canonical quotient topology. Both
characteristics of `k` are included, and `G` need not be split. The improper
parabolic is included.

## Proof

The proof applies three published theorems and adds nothing else.

1. `Langlands.Aubert.General.RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic`
   from [ArbitraryParabolicFiniteSupportReduction](ArbitraryParabolicFiniteSupportReduction.md)
   assumes `GroupScheme.ParabolicDynamicStatement.{u}` and
   `BruhatTits.DynamicParabolicQuotientCompactStatement.{u}`. From them it
   derives `CompactSpace (Induction.LeftQuotient (pointImage p))` for a
   connected reductive `G`, any `p : P ⟶ G` and any
   `hp : IsParabolicSubgroup p`. The quotient carries the topology
   `RationalPointFamily.pointTopology`, the same as in the target. The
   cocharacter supplied by the first statement has dynamic parabolic equal to
   the all-test range of `p`. Evaluating that equality on the identity test
   scheme rewrites `pointImage p` to the dynamic point subgroup. The second
   conjunct of the compactness statement then gives the conclusion for the
   `P(k) g` coset side.
2. `Langlands.GroupScheme.parabolicDynamic`, from
   [ParabolicDynamicProof](../../GroupScheme/Absolute/ParabolicDynamicProof.md),
   is the published unconditional proof of `ParabolicDynamicStatement.{u}`
   (Milne, Theorem 25.1). It discharges the first premise.
3. `Langlands.BruhatTits.dynamicParabolicQuotientCompact`, from
   [QuotientCompactProof](../../BruhatTits/Parabolic/QuotientCompactProof.md),
   is the published unconditional proof of
   `DynamicParabolicQuotientCompactStatement.{u}`. It discharges the second
   premise. That proof uses the algebraic flag quotient of a dynamic parabolic
   and compactness of the rational points of a proper scheme over a local
   field.

In Lean, the proof introduces the field data, `G` and `hG`. It then supplies
the instance `hG.isAffineHom`, which the helper takes as an implicit instance
argument. In the statement this instance appears only through an inlined
`haveI`, so it must be installed again in the proof. Since `IsAffineHom` is a
proposition, this copy is definitionally equal to the statement's, and so is
the point topology built from it. After introducing the two retained instance
binders, `P`, `p` and `hp`, the proof applies the helper to `parabolicDynamic`,
`dynamicParabolicQuotientCompact`, `hG`, `p` and `hp`.

The Hausdorff hypothesis on `k` and the two instance binders on
`rationalPoints G` stay in the proved type unchanged. The proof does not need
them, because the imported compactness theorem holds over every
nonarchimedean local field without them. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Scope and source

The proposition is the compactness assertion of Renard, *Représentations des
groupes réductifs p-adiques*, French edition dated 9 July 2026, V.5.1
Corollary, printed p.123 / PDF p.129 (source
`renard-2026-representations-groupes-reductifs-padiques`). Renard writes the
opposite coset side. The imported compactness theorem proves both coset
conventions, and the helper takes the `P(k) g` side, which is the target's
quotient. So no inversion step is needed here. The proof goes through the
dynamic description of parabolics and the algebraic flag quotient. It does not
follow Renard's route through an adapted compact subgroup. It proves no
conjugacy, Iwasawa decomposition, Jacquet admissibility or exponent finiteness
assertion.

Author: Worker 4777.
