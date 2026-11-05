# Actual Ore refinements along compatible quasi-isomorphisms

This is an internal construction from the actual reverse-map and subordinate
source-refinement constructions. It cites no new assertion from the literature.
The term Ore refers to the displayed commuting refinement square; this file
alone does not install a calculus-of-fractions instance.

## Objects, universes and assumptions

Work over a complete ultrametric normed field `K : Type u`. The actual atlas
presentations have ambient spaces in `Type v` and chart indices in `Type w`,
independently. Their chart algebras are presented affinoid algebras, realized
as finite positive-polyradius Tate quotients. A compatible strong map retains
its continuous ambient map and actual bounded algebra pullbacks for every
admissible original-chart pair, with spectrum equations, restriction
naturality and intrinsic local coefficient-test compatibility.

Fix compatible strong maps

```text
f : A → C,     s : B → C,
hs : s.toStrongHom.IsQuasiIso,
ha : A.atlas.HasAllLocalDomains,
hc : C.atlas.HasAllLocalDomains.
```

The full quasi-isomorphism condition means that the ambient map is a
homeomorphism and every admissible bounded pullback satisfies `Represents`
for its actual chart-image locus. This includes closedness, exact spectrum
image and unique bounded factorization for every presented-affinoid
coefficient test. Full-domain closure says that each actual local domain has
exactly the ambient locus of an original chart; it does not identify chosen
presentations of their algebras. These closure hypotheses are realized by
the existing constructed saturated presentations.

The arbitrary map `f` need not be a quasi-isomorphism. No full-domain closure
of `B`, chart directedness or upper-cofinality assumption is used. Composition
`f.comp g` means first `f`, then `g`.

## Closure of subordinate source selections

For an arbitrary strong map `t : A → D` and arbitrary target selection `P`,
`sourceSelectionForTarget_downward` proves that

```text
Q(i) := ∃ j, P(j) and t '' range(A.chart i) ⊆ range(D.chart j)
```

is a downward source selection. If chart `i` is contained in chart `i'`,
the image containment follows by `Set.image_mono`; the same selected target
chart witnesses membership of `i`. No downward property of `P` is needed.

When `A` has full-domain closure and `P` locally refines the target atlas,
`targetSubatlasSource_hasAllLocalDomains` applies the existing downward
subatlas closure lemma. The subordinate source was already constructed by
pulling finite relative target neighborhoods back to actual full source
domains and realizing their loci as original source charts. Thus its local
refinement and its new full-domain closure are proved properties of an
actual retained-chart presentation.

## Constructed source and two arrows

Use the existing reverse selection and its proved local refinement:

```text
P(j) := ∃ i, range(C.chart j) ⊆ s '' range(B.chart i),
R := hs.reverseSubpresentation hc,
r := hs.reverseCompatibleStrongMap s.coherent hc : R → B,
b := C.compatibleSubatlasInclusion P (proved refinement) : R → C.
```

These are existing actual constructions: the reverse map uses bounded
restrictions between the original chart algebras, and its full
quasi-isomorphism and compatibility are already proved. The existing whole
map identity is `r.comp s = b`. Target full-domain closure supplies the local
refinement of `P`; this is not an input output-object or covering assumption.

The new definitions are

```text
S := f.quasiIsoOreSource s hs ha hc,
a := f.quasiIsoOreInclusion s hs ha hc : S → A,
g := f.quasiIsoOreLift s hs ha hc : S → B.
```

Here `S` is exactly `f.toStrongHom.targetSubatlasSource ha P` with the proved
refinement. It keeps the space of `A` and selects the original source charts
whose complete `f` images lie in a selected chart of `C`. It retains their
original algebras, embeddings and bounded restrictions.
`quasiIsoOreSource_hasAllLocalDomains` proves its full-domain closure using
the downward-source lemma above.

The arrow `a` is the compatible subatlas inclusion, with identity ambient
map and all original bounded restrictions. The theorem
`isQuasiIso_quasiIsoOreInclusion` gives its full quasi-isomorphism property;
`quasiIsoOreInclusion_baseMap` records its literal continuous map.

Let `L := f.targetSubatlasLift ha P (proved refinement) : S → R`.
The lift `g` is defined as `L.comp r`. The map `L` retains all original
admissible bounded pullbacks of `f`; compatible composition supplies all
admissible bounded pullbacks of `g`, computed by bounded composition on any
admissible chain. In particular these are complete algebra maps rather than
only their induced functions on spectrum points. The theorem
`quasiIsoOreLift_baseMap` gives

```text
g.baseMap = hs.inverseBaseMap.comp f.baseMap.
```

## Full commuting square and uniqueness

`quasiIsoOre_square` proves the entire compatible-morphism equality

```text
g.comp s = a.comp f.
```

Associativity turns the left side into `L.comp (r.comp s)`. The existing full
reverse identity replaces `r.comp s` by `b`. The complete subordinate
source-refinement square gives `L.comp b = a.comp f`. Both intermediate
identities equate whole compatible maps, including all bounded pullbacks;
the argument does not infer bounded-map equality from the ambient equation.

`isQuasiIso_quasiIsoOreLift` additionally assumes that `f` is a full
quasi-isomorphism. The subordinate lift is then a full quasi-isomorphism,
as is `r`; the existing compatible composition theorem proves that `g` is
one too.

`quasiIsoOreLift_unique` states that any compatible `g' : S → B` satisfying
`g'.comp s = a.comp f` equals `g`. Apply full compatible cancellation along
`s` to that equality and the constructed square. The cancellation uses the
full bounded coefficient-test uniqueness of `hs`, without an extra domain
closure hypothesis. This uniqueness is on the specified constructed source
refinement, not a universal property among all possible source refinements.

Finally `CompatibleAtlasPresentation.quasiIsoOre_commSq` packages the same
constructed square as `CategoryTheory.CommSq` in the actual compatible-map
category. It introduces no new category or assumed morphism.

## Remaining scope

This unit constructs the general square for compatible maps with the stated
source and common-target closure hypotheses, and proves that the new source
retains full-domain closure. It does not yet provide a calculus-of-fractions
instance on the saturated category or compare the resulting localization
with an independently defined analytic-space category. Etale, quasi-etale
and equivariant sites, compact and distinguished domains, and the Harris
tower specialization remain obligations of the surrounding task.
