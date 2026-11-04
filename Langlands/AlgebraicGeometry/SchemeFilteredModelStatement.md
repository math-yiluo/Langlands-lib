# Model morphisms over the original filtered ring stages

`InitialRingModelDescent` states the relative Hom comparison and
prescribed-isomorphism conclusions of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(1), second assertion, and (3). It retains the
original ring system after a chosen stage. Initial-model existence and
the properties of part (2) are separate assertions.

Fix a small filtered category `J`, an actual ring diagram `F`, a cocone
`c` with `IsColimit c`, a chosen object `j₀`, and two arbitrary schemes
`X` and `Y` over `Spec (F.obj j₀)`. All sizes share arbitrary universe
`u`. The models may be nonaffine and nonseparated, and the original
ring transitions may be noninjective. The actual later-stage category
is `Under j₀`, whose objects record arrows out of `j₀`. For a directed
poset it is exactly the usual tail of stages greater than or equal to
`j₀`.

`InitialRingModelHomColimitComparison` uses the published
`initialRingAlgebraDiagram` and `initialRingAlgebraCocone`. Their rings,
structural algebra maps, transitions and cocone maps are the original
ones. The quotient `SpectrumHomColimit` is the concrete quotient of
the disjoint union of the relative Hom sets at these stages, and its
map is the actual `spectrumHomColimitMap`. In particular, the target
is the relative Hom set between the pullbacks along
`Spec.map (c.ι.app j₀)`, and the stage objects are the pullbacks along
`Spec.map (F.map j.hom)`. There are three conclusions:

1. The comparison is injective when `X.hom` is quasi-compact and
   `Y.hom` is locally of finite type.
2. It is surjective when `X.hom` is quasi-compact and quasi-separated
   and `Y.hom` is locally of finite presentation.
3. Under the latter hypotheses it is bijective, and the actual
   `spectrumHomCocone` has a colimit witness, expressed by `Nonempty`
   to keep the assertion proposition valued.

`InitialRingModelMorphismDescent` states the representative-level
conclusions explicitly. Under the hypotheses of conclusion 2, every
actual limiting relative morphism is the base change of one at a
later stage. Under the hypotheses of conclusion 1, two representatives
whose actual limiting morphisms agree become equal after restriction
along actual arrows `i → k` and `j → k` in `Under j₀`.
The maps `toLimit` and `restrict` are the published pullback-induced
maps; their naturality squares characterize their base changes.

The last clause assumes that both models have locally finitely
presented, quasi-compact and quasi-separated structural maps. This is
the source's finite-presentation condition over a general ring. Every
prescribed isomorphism between their limiting pullbacks which commutes
with the base projections descends to an isomorphism at one actual
later stage. Its base compatibility and equality with the prescribed
limiting morphism are part of the conclusion. Eventual uniqueness is
the preceding equality clause, applied to the underlying relative
morphisms of any two such isomorphisms. Equality of isomorphisms is
determined by equality of those morphisms; no uniqueness at the first
descent stage is asserted.

The separate weaker hypotheses and small filtered-category version
are derived strengthenings of Conrad's assertion. The original
finitely presented models satisfy all hypotheses for bijectivity and
prescribed-isomorphism descent. The construction's theorem
`initialRingAlgebraCoconeIsColimit` supplies the tail colimit witness
from the original ring-colimit witness; it is not an extra premise.
The proposed proof specializes `SpectrumModelHomColimitComparison`
and `ModelMorphismDescent` to these actual data and reindexes the
opposite stages. This pair defines propositions only and assumes no
Hom bijection or descent property as structure data. Arithmetic
identifications, topology, other morphism properties and whole-paper
completion remain separate obligations.
