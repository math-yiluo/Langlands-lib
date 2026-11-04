# Actual relative model morphisms over algebra diagrams

This internal construction specializes the actual model-morphism interfaces
of `SchemeLimitModelMaps` and `SchemeLimitModelColimit` to a diagram of
commutative algebras. Its motivating source is Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(1). That passage compares the directed colimit of Hom
sets of base-changed models with morphisms after base change to the
colimit ring. This file constructs that map and proves its comparison
with the generic scheme-diagram construction; it does not prove its
finiteness-dependent bijectivity.

Fix an arbitrary commutative ring `R`, a small category `J`, and an actual
functor `F : J ⥤ CommAlgCat R`. All carriers and index types share an
arbitrary universe `u`. The functor `spectrumDiagram R F` on `Jᵒᵖ` is
literally `F.op ⋙ algSpec (CommRingCat.of R) ⋙ Over.forget _`. Its objects
are the affine schemes `Spec (F.obj j)`. Its structure transformation
`spectrumStructure` consists of the given algebra maps to `Spec R`.

For any algebra cocone `c`, `spectrumCone` is the underlying scheme cone
of the already constructed `PointTopology.ringTestCone`. Its vertex is
`Spec c.pt`; its leg at `op j` is exactly the spectrum map of the algebra
homomorphism `c.ι.app j`. The structural map `spectrumBaseMap` is the
actual algebra spectrum map `Spec c.pt → Spec R`, and
`spectrumCone_compat` proves compatibility with each leg. When `J` is
filtered, an `IsColimit c` witness gives `spectrumConeIsLimit`, proving
that this cone is a scheme limit: reuse `ringTestConeIsLimit`, then
preservation of connected limits by the forgetful functor from schemes
over `Spec R`. Filteredness supplies the required nonempty connected
opposite index. No scheme-limit witness is assumed independently.

Let `X` and `Y` be arbitrary actual schemes over `Spec R`. They need not
be affine, separated, quasi-compact, or finitely presented for these
constructions. `SpectrumLevelHom R F X Y j` is the subtype of actual
scheme morphisms

`Spec (F.obj j) ×_{Spec R} X → Spec (F.obj j) ×_{Spec R} Y`

whose composition with the target's first projection is the source's
first projection. Thus it is precisely the relative Hom set over the
stage spectrum. Its transition along `r : i → j` is the actual
pullback restriction `restrict ... r.op`; the displayed functor map law
records that formula.

The functor `spectrumHomFunctor` uses the original algebra index `J`.
It is the generic opposite-index Hom functor precomposed with Mathlib's
`opOp J`. `SpectrumHomColimit` is its concrete `ColimitType` quotient of
the disjoint union of the stage Hom sets. The canonical classes
`spectrumHomColimitι` identify a stage morphism with its restriction
along each algebra transition.

The equivalence `spectrumHomColimitEquiv` compares this quotient with
the generic `HomColimit` for `spectrumDiagram`. Both directions are
constructed by the quotient universal property, sending a stage
representative to the same stage morphism, with `op` or `unop` on its
index. The inverse laws follow by choosing a stage representative.
This is a proved comparison between the two concrete quotients,
without a bijectivity or filteredness assumption.

Finally, `spectrumHomCoconeTypes` and `spectrumHomCocone` are the actual
base-change cocones reindexed by `J`. Their point is the actual
relative Hom set between the two pullbacks over `Spec c.pt`.
The induced `spectrumHomColimitMap` sends each stage class to its
actual pullback morphism over `Spec c.pt`. Its representative formula
is definitional. The equation `spectrumHomColimitMap_eq` proves that
the new comparison is the generic `homColimitMap` after the proved
quotient equivalence.

Filteredness and finiteness assumptions are unnecessary for the
constructions and quotient comparisons; the scheme-limit adapter
`spectrumConeIsLimit` requires filteredness. A separate target and
proof will specialize the generic model Hom-colimit theorem when `J`
is filtered. The initial existence of finitely presented models,
property descent, prescribed-isomorphism descent, the choice of a
tail after an initial ring stage, arithmetic realizations, and
topology remain separate assertions. No such substantive assertion
is stored as an assumed structure field here.
