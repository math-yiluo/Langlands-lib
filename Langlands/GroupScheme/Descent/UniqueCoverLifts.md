# Descent coherence from unique pullback lifts

Worker 416. This internal construction transfers actual group-scheme Čech
descent data along a supplied map that admits unique lifts of isomorphisms
between all pullbacks of its target. It constructs the source overlap
isomorphism and proves its cocycle. It does not establish existence of
universal covers, existence of such lifts, or effective descent.

For actual group schemes `C` and `H` over any scheme `S : Scheme.{u}` and
an actual homomorphism `π : C ⟶ H`, `HasUniquePullbackIsoLifts π` is a
proposition. For every scheme `T : Scheme.{u}`, two maps `f g : T ⟶ S`,
and an actual isomorphism `e : f*H ≅ g*H`, it requires a unique actual
homomorphism `a : f*C ⟶ g*C` such that

```text
a ≫ g*π = f*π ≫ e.hom.
```

This hypothesis is about schemes, including nonfield double and triple
overlaps. It is stronger than the Library's field-only universal property
of a supplied simply connected cover. The latter alone is not used as if
it applied on arbitrary overlaps. The module assumes neither that an
arbitrary central cover has canonical descent nor that an arbitrary group
over an extension field descends. Establishing this hypothesis for the
universal cover is a separate structural obligation.

The implemented `HasUniquePullbackIsoLifts.lift` chooses the unique
homomorphism. `lift_fac`, `lift_unique` and `hom_ext` express its defining
equation and uniqueness. The identity map lifts the identity isomorphism,
and the composite of two lifts lifts the composite target isomorphism.
Uniqueness therefore gives `lift_refl` and `lift_trans`. Applying this to
an isomorphism and its inverse constructs `liftIso`, an actual
isomorphism between the pulled-back sources.

The comparison is compatible with further pullback. `pullHom_lift` pulls
back the defining equation using the actual `pullHom` and its endpoint
comparisons in `Descent.Data`. Its composition and base-change laws show
that the resulting map lifts `pullIso` of the target isomorphism.
Uniqueness identifies it with the chosen lift. `pullIso_liftIso` is the
corresponding equality of actual isomorphisms.

For any `p : S ⟶ B` and actual target datum `D : Datum p H`, `Datum.lift`
uses `liftIso` of `D.overlap` on the double overlap. Pullback compatibility
identifies its three restrictions to the triple overlap with the lifts of
the target's three restrictions. Preservation of composition and the
target cocycle show that these source restrictions satisfy the cocycle.
Thus the source datum is constructed without assuming its overlap
isomorphism or its cocycle. `Datum.compatible_lift` proves that `π` respects
the two data, with the direction prescribed by `Compatible` in
`Descent.Data`. `Datum.lift_unique` proves that every compatible source
datum equals this one.

In particular, when `H` is the actual pullback of a group over `B`, the
published `canonicalDatum p` supplies `D`. The construction then produces
the compatible source datum required by an effectivity theorem, provided
the stated unique-lifting hypothesis has been proved. No flatness,
surjectivity, finite Galois condition, affineness, semisimplicity or
simple connectedness is required for this coherence deduction. Those
conditions belong to proofs of its hypothesis or to later descent steps.

Provenance is internal: the construction uses only actual pullback
comparisons and their functoriality in `Descent.Data`, together with
uniqueness of the explicitly supplied lifts. No external classification,
field-extension or descent theorem is asserted.
