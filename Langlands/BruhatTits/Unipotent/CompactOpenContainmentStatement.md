# Compact-open containment in actual dynamic unipotent radicals

`Langlands.BruhatTits.DynamicUnipotentCompactOpenContainmentStatement`
states that every compact subset of the actual dynamic unipotent radical
is contained in a compact open subgroup of that same radical. This is a
Prop-valued statement definition; the module supplies no proof.

## Exact objects, hypotheses and topology

The closed proposition quantifies over every universe-polymorphic field
`F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`, every actual
`G : Langlands.GroupScheme (Spec (CommRingCat.of F))`, a proof
`hG : Langlands.GroupScheme.IsConnectedReductive G`, and every rational
cocharacter

```text
χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G.
```

The local-field hypothesis relates the topology to the valuation and supplies
the nontrivial locally compact nonarchimedean setting. It allows both equal
and mixed characteristic. The reductive hypothesis is the published actual
smooth, connected, affine group-scheme predicate with trivial geometric
unipotent radical. No splitness, quasi-splitness, tameness or positive-rank
condition is imposed.

The ambient group is the existing group of relative scheme morphisms

```text
Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X.
```

Its multiplication is the published group-scheme point multiplication.
The definition installs `hG.isAffineHom` and derives `IsAffine G.X.left`
before explicitly binding its topology to
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`.
That named construction induces the existing affine evaluation topology on
`RingPoint F G.X F` along `rationalPointEquiv F G.X`.
`rationalPointHomeomorph F G.X` is the corresponding named homeomorphism;
the underlying scheme maps are preserved. No additional topology on the
ambient carrier is quantified over.

The subgroup used in the conclusion is exactly

```text
U := (Langlands.GroupScheme.Dynamic.unipotent χ).carrier
  (Over.mk (𝟙 (Spec (CommRingCat.of F)))).
```

It has its existing subgroup group law and the subtype topology inherited
from the explicitly bound ambient topology. The compactness and openness
in the conclusion both refer to this topology on `U`:

```text
∀ C : Set U, IsCompact C →
  ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ C ⊆ (K : Set U).
```

In particular, the containing subgroup belongs to the same actual `U`,
and its openness is relative to `U`. The compact set may be empty.
Every rational cocharacter is allowed, including the trivial one;
there is no exclusion of a trivial radical, `U = ⊥`, or an empty
relative root set. Applying the universal target to the opposite
cocharacter gives the corresponding assertion for that dynamic radical
without introducing an unrelated carrier.

## Original source and derived formulation

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, V.5.2(iii), printed page 123 /
PDF page 129. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original was read directly, and page 129 was visually checked
to preserve the opposite-radical bars and conjugation signs. A bounded
filename search found no source-specific errata note in the current
Library or project notes.

For a suitable compact open `K`, Renard gives the two power exhaustions
of the opposite radicals, explicitly observes that a parabolic unipotent
radical is the union of its compact open subgroups, and then states stronger
uniform containment of compact subsets in expanding conjugates of the
corresponding `K ∩ N` or `K ∩ N̄`. Those intersections are compact open
in the respective radicals, and conjugation preserves compactness and
relative openness. The present target isolates the existence of one such
containing compact open subgroup for each compact set. It does not
translate the whole theorem.

The actual radical is expressed using the shared dynamic construction:
`Dynamic.unipotent χ` consists of the points whose algebraic conjugation
orbit `t ↦ χ(t) g χ(t)⁻¹` extends to the affine line with value the
identity at zero. For connected reductive groups this is the dynamic
description of the unipotent radical of the cocharacter parabolic.
Using that description and the owning rational-point topology makes
this a derived formulation of Renard's compact-containment consequence,
rather than a new abstract group supplied with a containment certificate.
Any radical identification or topological compatibility used in a future
Lean proof remains a proof obligation; this statement does not establish it.

Renard attributes V.5.2 to his reference [24], section 2.1, namely
Deligne, *Le “centre” de Bernstein*. This records Renard's attribution;
no independent reading of that external original is claimed here.
The algebraic objects and topology are imported from
`Langlands.GroupScheme.Dynamic.Basic`,
`Langlands.GroupScheme.Reductive.Basic` and
`Langlands.AlgebraicGeometry.PointTopology.RationalPoints`, with no
parallel reductive-group or rational-point construction.

## Scope and remaining obligations

No exhaustion, containing compact-open family, chamber-nonemptiness
witness or arbitrary-topology certificate is an input. A future structural
proof must construct or prove every such ingredient it uses on the
actual objects. A set-theoretic union alone does not justify uniform
compact containment; an exhaustion route must supply an appropriate
open nested cover and prove compactness of the containing subgroup.

The separate successor that forgets openness may derive
`Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups U` by taking
the underlying subgroup of the resulting `OpenSubgroup U`. Neither that
deduction nor a structural proof of this target is supplied here.
Jacquet exactness, unimodularity and the other representation-theoretic
obligations remain separate.

The [shared Chapter V source ledger](../../../notes/renard/chapter-v-structural-inputs.md)
retains the full S19–S23 and D07 obligations: all five S19 properties;
the same normal compact-open neighborhood basis in S20; simultaneous
Iwahori decompositions and both contraction signs in S21; both S22
exhaustions and both uniform compact-subset clauses; and both S23
neighborhood bases and uniform compact-open cofinality clauses. Actual
characters, chamber nonemptiness, including rank zero, and their
comparisons remain construction and proof work. This focused statement
closes none of those larger targets or existing task holds.
