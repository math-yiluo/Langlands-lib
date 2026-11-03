# Actual Čech descent data for group schemes

Author: Worker 1442.

This module defines actual Čech descent data, compatible homomorphisms, the
canonical datum on a base change, and a separate solution witness. All names
below are in `Langlands.GroupScheme.Descent`. For an arbitrary morphism
`p : S ⟶ B` of schemes in universe `u`, the group schemes are the existing
`Langlands.GroupScheme S = Grp (Over S)`. Pullback is the existing actual
`Langlands.GroupScheme.baseChange`, including its induced group operations.
The group schemes may be noncommutative.

## Source and scope

The underlying scheme-descent definition is J. S. Milne, *Algebraic Groups*
(2017), Appendix A.81, printed p.585 / PDF p.601. Registered source:
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The original page, including its displayed cocycle, was read and rendered.
The retained official errata snapshot of 2026-11-02 was consulted; it contains
no correction to A.81.

Milne defines an isomorphism from the first pullback of a scheme to the second
pullback and imposes its triple-overlap cocycle. He also describes the canonical
datum on a scheme obtained by base change. His passage assumes a faithfully flat
morphism of algebraic schemes over a field and goes on to discuss effectivity.
Here the datum, compatible morphisms, canonical datum, solution witness and
transport helpers are derived packaging in the existing category of actual
group objects. The definitions and elementary constructions make sense for
arbitrary `p`; they use no flatness, surjectivity, affineness, finiteness or
field hypothesis. In particular they apply to `Spec L ⟶ Spec k` for arbitrary
field extensions in this universe. No general solution-existence or
effectivity assertion from A.81 is included.

## Actual overlaps and comparisons

`Overlap p` is `pullback p p`, with projections `fst p` and `snd p`.
`Triple p` is the actual pullback
`pullback (snd p) (fst p)`. Thus it describes two overlaps sharing their middle
coordinate. Its two projections are `p12 p` and `p23 p`. The coordinate maps are

```text
p1 = p12 ≫ fst
p2 = p12 ≫ snd = p23 ≫ fst
p3 = p23 ≫ snd.
```

`p23_fst` is the middle-coordinate equality, coming from the pullback
condition. The map `p13 p` is the actual `pullback.lift` of `p1 p` and `p3 p`;
their composites to `B` agree by the double- and triple-pullback conditions.
The equations `p13_fst` and `p13_snd` identify its coordinate projections.
There is no implicit identification of differently parenthesized pullbacks.

For `f : T ⟶ S`, `q : U ⟶ T`, `r : U ⟶ S`, and `h : q ≫ f = r`,
`pullbackComparison f q r h G` has direction

```text
q*(f*G) ≅ r*G.
```

It is the inverse of the existing `baseChangeCompIso f q G`, followed by
`eqToIso` for the equality of composite base morphisms. The reused comparison
is in `Langlands.AbelianScheme.Tate.BaseChangeCoherence`; its group-scheme
part applies without commutativity. The theorems
`pullbackComparison_hom_fst` and `pullbackComparison_inv_fst` say that the
comparison preserves the projection to the original scheme underlying `G`.
Their proofs reduce to the existing comparison's projection formula and its
inverse law. `pullbackComparison_naturality` is naturality for an actual
group-scheme homomorphism, inherited from the lifted pullback-composition
natural isomorphism.

`pullHom q hf hg a` first uses the inverse comparison at its source, then
`(baseChange q).map a`, then the forward comparison at its target. Consequently
its endpoints are the direct pullbacks specified by `hf` and `hg`.
`pullIso` uses the same comparisons for isomorphisms, and `pullIso_hom`
identifies its forward morphism with `pullHom`.
`pullHom_id`, `pullHom_comp` and `pullHom_map` prove identity, composition and
base-changed-homomorphism formulas by functoriality, inverse cancellation and
comparison naturality.

## Datum and compatible morphisms

`OverlapIso p G` is the actual group-scheme isomorphism

```text
(baseChange (fst p)).obj G ≅ (baseChange (snd p)).obj G.
```

Its direction is coordinate 1 to coordinate 2. The isomorphisms `iso12 e`,
`iso23 e`, and `iso13 e` pull this isomorphism back along the corresponding
triple-overlap projections using `pullIso`. Their endpoints are respectively
`p1*G ≅ p2*G`, `p2*G ≅ p3*G`, and `p1*G ≅ p3*G`. The comparison equalities
are `rfl, rfl` for `p12`, `p23_fst, rfl` for `p23`, and
`p13_fst, p13_snd` for `p13`.

`Cocycle e : Prop` is exactly

```text
(iso12 e).hom ≫ (iso23 e).hom = (iso13 e).hom.
```

Lean's `a ≫ b` means first `a`, then `b`: transport 1 to 2 and then 2 to 3
equals direct transport 1 to 3. Milne's displayed formula uses the subscripts
`31`, `32`, `21` and ordinary right-to-left composition. This module fixes
the endpoint notation `12`, `23`, `13` explicitly as above; the endpoint
description specifies the convention independently of printed projection
subscripts.

`Datum p G` has precisely two fields: `overlap : OverlapIso p G` and
`cocycle : Cocycle overlap`. `Datum.ext` reduces equality of data to equality
of overlap isomorphisms, using proof irrelevance for the cocycle proofs.

For `D : Datum p G`, `E : Datum p H`, and an actual group-scheme homomorphism
`f : G ⟶ H`, `Compatible D E f : Prop` is the commutative overlap square

```text
(baseChange (fst p)).map f ≫ E.overlap.hom =
  D.overlap.hom ≫ (baseChange (snd p)).map f.
```

`compatible_id` and `Compatible.comp` give identity and composition.
`Compatible.inv` proves compatibility of the inverse of a compatible
isomorphism by cancelling its two invertible base-changed morphisms.

For an isomorphism `e : G ≅ H`, `transportOverlap D e` has forward morphism

```text
(fst p)*e.inv ≫ D.overlap.hom ≫ (snd p)*e.hom.
```

`Datum.transport D e` equips it with its cocycle. The proof pulls the
conjugation formula to each pair of triple coordinates using `pullHom_comp`
and `pullHom_map`, cancels the middle `e.hom/e.inv` pair, and applies
`D.cocycle`. `Datum.compatible_transport` and
`Datum.compatible_transport_inv` give compatibility of `e.hom` and `e.inv`.
`Datum.transport_refl`, `Datum.transport_trans`, and `Datum.transport_symm`
give transport by identity, by a composite, and back by the inverse.
`Datum.transport_eq` identifies a target datum with the transported datum
whenever the isomorphism is compatible. These equalities follow by
extensionality and the displayed conjugation formula.

## Canonical datum and solutions

For `C : GroupScheme B`, `canonicalOverlap p C` compares both iterated
pullbacks of `p*C` with the single direct pullback `(fst p ≫ p)*C`.
It first applies `pullbackComparison p (fst p) (fst p ≫ p) rfl C`,
then the inverse of
`pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm C`.
The explicit equality in the second comparison is
`snd p ≫ p = fst p ≫ p`. Thus this canonical overlap again goes from
the first pullback to the second.

`canonicalOverlap_fst` says that this isomorphism preserves the projection
to `C`; `pullHom_canonicalOverlap_fst` gives the same property after another
pullback. The canonical cocycle in `canonicalDatum p C` is proved by comparing
the two morphisms' underlying projections to `C`. The private helper
`hom_ext_original` justifies this comparison: use the canonical isomorphism
from an iterated pullback to the direct pullback, then the pullback universal
property, with the projection to the base fixed by being a morphism over that
base. The two cocycle composites preserve the same projection to `C`.
`canonicalDatum_compatible` proves that `(baseChange p).map a` is compatible
with the canonical data for every actual homomorphism `a : C ⟶ D`, by the
same extensionality and projection formulas.

`Solution D` is a separate structure with fields

```text
obj        : GroupScheme B
iso        : (baseChange p).obj obj ≅ G
compatible : Compatible (canonicalDatum p obj) D iso.hom.
```

`canonicalSolution p C` solves `canonicalDatum p C`, using `obj := C` and
the identity isomorphism. `Solution.mapIso s e he` composes a solution's
identification with any compatible isomorphism `e`; compatibility follows
from `Compatible.comp`. `Solution.transport s e` specializes this construction
to `Datum.transport`, retaining the same object over `B` and composing the
identification with `e`.

A datum stores neither a descended object nor a solution. The canonical
solution and transport constructions do not assert a solution for arbitrary
data. Existence of solutions, affine effectivity, descent of additional
geometric properties and any uniqueness theorem remain separate results.
