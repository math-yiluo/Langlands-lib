# Internal star-sheaf cokernel and section-universe targets

Worker 1599 states these targets from Worker 709's internal size-scope design
and specification. The actual diagram is the published construction by
Worker 1301 with Worker 709 in [StarDiagram](StarDiagram.md). This pair defines
three propositions and their named conjunction. It proves only the short
canonical-zero compatibility laws described below; exact proofs of the three
targets belong to a separate successor.

## Provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
II.2.1, printed pp.33–34 / one-based PDF39–40, defines normalized
chosen-basis presheaves, their natural morphisms and the literal unique-gluing
condition for sheaves. A.VI.1, printed p.261 / PDF267, includes abelian-group
sheaves among its motivating abelian-category examples. These pages were
reread for this pair.

Those passages supply the source interfaces and motivation. The star diagram,
the proposed injection and both universe-size obstructions are internal
derived content, not assertions printed in Renard. This pair claims no
discrepancy in the printed mathematics.

## Actual category and canonical zeros

All four proposition names below belong to
`Langlands.Sheaf.Renard.StarDiagram`. The module imports the existing
`StarDiagram` by Lean name and uses its named `topology I` on `Option I`.
Its opens are exactly the empty set and sets containing `none`. The topology
is installed only inside local scopes or proposition bodies.

For `I : Type u`, the actual category is
`BasisSheaf.{u,v} (allOpenBasis (Option I))`, with section carriers in
`Type v` independently of `u`. Its objects retain the published normalized
functors and literal `SheafCondition`; its morphisms are the original natural
transformations under `sheafHomEquiv`. No comparison category, sheafification
or replacement topology is introduced.

The actual published `F`, `G`, `Ti i`, `f` and `gi i` are retained.
On nonempty opens `F` and `G` have lifted integer coefficients; `F` doubles
restriction from a leaf-containing open to `E = {none}`, while `G` has
identity restrictions. The source morphism `f : F ⟶ G` doubles on
leaf-containing opens and is the identity on `E`. The actual `Ti i` is the
lifted mod-two skyscraper at `some i`, and `gi i : G ⟶ Ti i` reduces integers
modulo two on neighborhoods of that point.

Canonical zero morphisms are supplied by Mathlib's existing preadditive
structure on `AddCommGrpCat`, its pointwise functor-category structure, and
`Preadditive.fullSubcategory` applied to the normalized presheaves and then
the sheaves. These are constructed instances, not hypotheses.
`sheafHomEquiv_zero_app` is reflexivity after unwrapping these structures:
each component is the actual zero additive homomorphism.
`f_comp_gi_eq_zero` applies injectivity of `sheafHomEquiv`, extensionality of
natural transformations and the published `f_gi_component_zero` law.
Thus the diagram's existing zero composite agrees with the precise zeros
used by the categorical cokernel interfaces. Neither compatibility lemma
assumes abelianness or existence of a cokernel.

## The three proposition definitions

`CokernelSectionInjectionStatement.{u,v}` is the closed proposition

```text
∀ (I : Type u),
  letI : TopologicalSpace (Option I) := topology I
  ∀ (c : CokernelCofork (f.{u,v} (I := I))),
    IsColimit c → Nonempty (I ↪ Sections c.pt.obj.obj (whole I)).
```

Here `CokernelCofork f` is Mathlib's actual `Cofork f 0`.
It consists of an actual sheaf vertex `c.pt` and cofork data; its arrow
`c.π : G ⟶ c.pt` annihilates `f` with the canonical zero just described.
`IsColimit c` asserts the actual universal property, including unique
factorization through this cofork for every sheaf-valued annihilating arrow.
The proposition quantifies over every cofork and every such colimit
structure, without choosing or assuming a cokernel.

The expression `Sections c.pt.obj.obj (whole I)` evaluates the vertex's
original underlying section functor on the published whole-space open.
`Sections` returns an actual `AddCommGrpCat.{v}` object; the embedding
notation coerces that object to its carrier in `Type v`.
Thus the conclusion is existence of an injective function from the actual
leaf index type `I` into that actual group of global sections.
The only universally supplied data are `I`, `c` and its colimit structure.
There is no hypothesis of inhabitance, a size bound, a relation between
`u` and `v`, abelianness, or extra topological properties. Empty `I` is
included.

`UndersizedNoCokernelStatement.{v}` installs `topology (Type v)` and states

```text
¬ HasCokernel (f.{v + 1,v} (I := Type v)).
```

The index type `Type v` and its star space `Option (Type v)` lie in
`Type (v+1)`, whereas every section carrier remains in `Type v`.
Mathlib's `HasCokernel f` is `HasColimit (parallelPair f 0)` in the
actual original category. Its negation concerns existence of any
categorical cokernel, rather than a particular candidate construction.
It is a closed target with no additional hypotheses.

`UndersizedNotAbelianStatement.{v}` uses the same topology and states

```text
¬ Nonempty (CategoryTheory.Abelian
    (BasisSheaf.{v + 1,v} (allOpenBasis (Option (Type v))))).
```

This is absence of any Mathlib `Abelian` structure on the existing category
and its existing category instance. `Abelian` is data-bearing, hence the
`Nonempty` wrapper before negation. No abelian structure is supplied as a
premise; the target concerns the actual section-size category itself.

`CokernelScopeStatements.{u,v}` is the closed conjunction

```text
CokernelSectionInjectionStatement.{u,v} ∧
  UndersizedNoCokernelStatement.{v} ∧ UndersizedNotAbelianStatement.{v}.
```

The universe parameters are explicit: `u` and `v` remain independent in
the first conjunct, and each negative conjunct specializes the space
universe to `v+1` with section universe `v`. Universes are Lean declaration
parameters, rather than term-level quantified values. The aggregate is
the exact target supplied for a separate proof successor.

## Relation to sufficient section universes

The separate positive
[`Langlands.Sheaf.Renard.BasisSheafAbelianStatement`](SheafAbelianStatements.md)
universally quantifies a space `X : Type u`, its supplied topology and its
chosen basis `B`, with conclusion
`Nonempty (Abelian (BasisSheaf.{u,max u v} B))`.
Its sections lie in a universe at least as large as the space universe.
For the present star space on `Type v`, that sufficient section universe
is at least `v+1`; the two negative targets instead fix sections in
`Type v`. The categories have different allowed section sizes, so these
targets do not contradict the positive target.

The sufficient size is internal formalization data, not a printed
hypothesis or a necessity claim for every space. The statements here
assert the proposed obstruction for this particular internal star
specialization only. They add no total disconnectedness, local
compactness, Hausdorffness or countability premise, and they leave the
positive sheaf statements and the normalized-presheaf branch unchanged.
This pair supplies statement targets and compatibility lemmas only;
neither the injection nor either obstruction is proved here.
