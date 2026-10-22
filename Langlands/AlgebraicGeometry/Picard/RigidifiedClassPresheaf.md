# The presheaf of rigidified line-bundle classes

For a scheme morphism `f : X → S` with an actual section `ε : S → X` and a
proof `ε ≫ f = id_S`, this module constructs the set-valued presheaf
`RigidifiedLineBundle.classPresheaf` on `Over S`. Its value at an `S`-scheme
`T` is the quotient of actual rigidified line bundles on `T ×_S X` by
isomorphism. Its restriction along `h : T → U` is induced by the canonical
relative pullback already constructed in `RigidifiedLineBundle`.

The construction has an explicit proof parameter
`coherence : RigidifiedModule.PullbackCoherenceStatement`. That proposition is
the conjunction of the identity and composition compatibility targets in
`RigidifiedPullbackStatements`. This module does not prove those targets or
assume them through a new axiom or global instance. It constructs the presheaf
conditional on a proof of precisely that proposition. The object types
`Classes` and map functions `classesPullback` themselves do not require the
proof; it is used to prove the functor laws.

In `Langlands.SchemeModule.RigidifiedModule`, `pullbackId` and `pullbackComp`
lift the existing scheme-module comparison isomorphisms to rigidified modules.
The two compatibility hypotheses allow `isoMk` to supply their rigidification
conditions. Naturality follows from naturality of the original module
comparisons and extensionality of the compatible-morphism subtype. For
consecutive squares with `f : X' → X`, `f' : X'' → X'`, the composition
comparison goes from `f'* (f* M)` to `(f' ≫ f)* M`.

In `Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle`, the corresponding
`pullbackId` and `pullbackComp` lift these natural isomorphisms to the full
subcategory whose underlying module is locally free of rank one.
`pullbackCongr` identifies pullbacks along equal maps; equality elimination
and proof irrelevance make it independent of the chosen square witnesses.
`relativePullbackId` and `relativePullbackComp` specialize the comparisons to
the actual relative fibre-product family. Functoriality of `relativeSpace`
and naturality of `relativeSection` supply the needed equations of scheme
maps and commutativity of the composite square.

`Classes f ε section_eq T` is literally
`Quotient (isIsomorphicSetoid (relative f ε section_eq T))`. Thus it identifies
two objects exactly when a compatible rigidified isomorphism exists.
`classesPullback` is `Quotient.map` on the actual relative pullback functor;
its well-definedness uses that functor's `mapIso`. The two laws of
`classPresheaf` are proved by quotient induction and `Quotient.sound`, using
respectively `relativePullbackId` and the inverse of
`relativePullbackComp`. This yields a functor
`(Over S)ᵒᵖ ⥤ Type (u + 1)`. No smallness reduction is asserted.

The original reference is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
Chapter VI §1, (6.2), printed p.88 (PDF p.92), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source defines the rigidified functor by isomorphism classes and describes
its pullback. This module constructs its underlying set-valued functor,
conditional on the stated canonical comparison laws. It uses `T ×_S X` in
place of the source's `X ×_S T`, with the canonical symmetry supplied by
`RelativeGeometry`. The explicit quotient and comparison packaging are
internal categorical constructions.

The source's quasi-compactness, quasi-separatedness and universal
pushforward condition enter later automorphism and Picard comparison results;
none of those conclusions is asserted here. Tensor products, the abelian
group law, comparison with the fppf Picard sheaf, representability and
Poincaré bundles remain separate obligations. No triangle or pentagon
identity for the lifted natural isomorphisms is claimed: the displayed
identity and composition isomorphisms suffice for equality on classes.
