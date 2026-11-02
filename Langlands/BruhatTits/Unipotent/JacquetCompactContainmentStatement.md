# Jacquet compact-subgroup containment in actual dynamic unipotent radicals

`Langlands.BruhatTits.DynamicUnipotentIsLimitOfCompactSubgroupsStatement`
is a conditional proposition: **if** the published structural statement
`Langlands.BruhatTits.DynamicUnipotentCompactOpenContainmentStatement`
holds, **then** every actual dynamic unipotent radical satisfies the
existing Jacquet predicate
`Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups`. It is a
Prop-valued statement definition; the module supplies no proof of the
implication and no proof of its premise.

## The exact implication

At each universe `u`, the proposition is

```text
DynamicUnipotentCompactOpenContainmentStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    (hG : Langlands.GroupScheme.IsConnectedReductive G)
    (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    [bindings below]
    IsLimitOfCompactSubgroups
      ((Langlands.GroupScheme.Dynamic.unipotent χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))).
```

The premise is the whole closed S22 proposition at the same universe `u`,
that is, compact-open containment for every local field of `Type u`, every
connected reductive group and every rational cocharacter. It is visible as
the hypothesis of the implication and is not asserted here. The conclusion
quantifies over exactly the telescope of that statement: the field `F`
with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, the actual group scheme `G` over
`Spec F`, the explicit proof
`hG : Langlands.GroupScheme.IsConnectedReductive G`, and the rational
cocharacter `χ`.

## Objects and topology

The bindings are those of the S22 statement, in the same order:
`hG.isAffineHom` is installed as `IsAffineHom G.X.hom`, then
`IsAffine G.X.left` is derived by `isAffine_of_isAffineHom G.X.hom`, and
then the topology on the identity-test point group

```text
Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X
```

is explicitly bound to
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`.
The group law on this hom-set is the published group-scheme point
multiplication (opened by `open scoped CategoryTheory.MonObj`, as in the
S22 module). No other topology on the ambient carrier is quantified over.

The subgroup in the conclusion is the same actual radical as in S22,

```text
U := (Langlands.GroupScheme.Dynamic.unipotent χ).carrier
  (Over.mk (𝟙 (Spec (CommRingCat.of F)))),
```

the points whose conjugation orbit `t ↦ χ(t) g χ(t)⁻¹` extends to the
affine line with value the identity at zero. It carries the subtype
topology inherited from the bound ambient topology. No new radical,
carrier or topology is introduced, and nothing is compared with an
unrelated group.

## The conclusion

`IsLimitOfCompactSubgroups` is the published predicate from
`Langlands.Representation.Jacquet.LocalizationExactnessStatement`. For
this `U` it unfolds to

```text
∀ C : Set U, IsCompact C →
  ∃ K : Subgroup U, IsCompact (K : Set U) ∧ C ⊆ (K : Set U),
```

with both compactness conditions taken in the inherited topology on `U`.
The predicate takes an ambient group with a topology as ordinary
parameters; forming it needs no `IsTopologicalGroup` instance, and the
statement adds none. The S22 conclusion differs only in asking for
`K : OpenSubgroup U`; the present conclusion forgets the openness.

## Retained scope

Nothing is excluded beyond the S22 telescope: equal and mixed
characteristic local fields, every connected reductive group (including
nonsplit and non-quasi-split groups), every rational cocharacter
(including the trivial one, so trivial radicals `U = ⊥`, empty relative
root sets and rank zero are all included) and the empty compact set. No
continuity, topological-group, exhaustion, chamber-nonemptiness or
neighborhood-basis premise is added.

## Intended proof route

A proof applies the premise at the same `F`, `G`, `hG`, `χ` and compact
`C`, obtaining a compact open subgroup `K : OpenSubgroup U` with
`C ⊆ K`. Its underlying subgroup `K.toSubgroup` has the same carrier
set, so its compactness and the containment of `C` are unchanged. That
proof is a separate successor; it does not prove the structural premise.

## Provenance

This is a derived adapter, not a new theorem printed in the source. It
connects the accepted S22 statement to the existing Jacquet predicate.
The S22 statement is itself derived from David Renard, *Représentations
des groupes réductifs p-adiques*, French version dated 9 July 2026,
V.5.2(iii), printed page 123 / PDF page 129 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
There Renard writes the radical as the union of expanding conjugates of
a compact open `K ∩ N`, observes that the unipotent radical of a
parabolic subgroup is therefore the union of its compact open subgroups,
and states that each compact subset lies in one such conjugate.
Forgetting openness of that containing subgroup is the condition
`IsLimitOfCompactSubgroups`, whose own provenance (the literal condition
before Bernstein–Zelevinsky 1977, Proposition 1.9) is recorded with the
published Jacquet statement. Renard attributes V.5.2 to his reference
[24], section 2.1; no independent reading of that reference is claimed.
The page was reread against the registered file for this statement.

## What remains separate

This statement does not prove S22, the forgetting-openness deduction,
Jacquet or character-localization exactness, unimodularity of the
radical, or any other S19–S23 assertion recorded in the
[Chapter V source ledger](../../../notes/renard/chapter-v-structural-inputs.md).
Comparisons of the rational-point topology and of the dynamic radical
with classical parabolic radicals also remain separate work.
