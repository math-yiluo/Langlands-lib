# Spreading invertibility of an actual line-bundle section

`Langlands.AlgebraicGeometry.Modules.ProperLineBundleMorphismSpreadStatement.{u}`
is a proposition definition. This module states an internal prerequisite for the
local two-axis triviality proof and supplies no proof.

For arbitrary schemes `X S : Scheme.{u}`, a universally closed morphism
`f : X ⟶ S`, an actual line bundle `L : LineBundle X`, a morphism
`φ : Langlands.Scheme.Modules.structureSheaf X ⟶ L.obj`, and a point `s : S`,
the hypothesis says that the actual pullback of `φ` to the scheme-theoretic
fibre `f.fiber s` is an isomorphism. The conclusion supplies an open
`U : S.Opens` containing `s` such that the pullback of the same morphism `φ`
along `pullback.fst f U.ι : X ×_S U ⟶ X` is an isomorphism.

Here `structureSheaf X` is `SheafOfModules.unit X.ringCatSheaf`, the structure
sheaf as a module over itself, and `LineBundle X` is the Library's full
subcategory of locally free rank-one module sheaves. A morphism
`O_X ⟶ L.obj` is the morphism attached to a global section of `L`; the
statement uses the morphism directly. Both occurrences of `IsIso` refer to
morphisms in Mathlib's actual categories of sheaves of modules on schemes, and
both pullbacks are Mathlib's `Scheme.Modules.pullback` functors applied to `φ`.
The fibre `f.fiber s` is the pullback of `f` along `S.fromSpecResidueField s`
and `f.fiberι s` is its first projection, so the hypothesis concerns the
fibre's full scheme structure. The conclusion concerns the whole base change
over `U`, including nilpotents.

Besides universal closedness of `f`, no hypothesis is made. In particular
there is no separatedness, finite-type, properness, projectivity, flatness,
smoothness, reducedness, noetherian, or cohomological premise, and no
replacement section or fibrewise-only triviality predicate. The universe `u`
is arbitrary.

## Provenance and scope

This is a derived internal statement that isolates the final topological step
in the proof of the Stacks Project's
`lemma-H1-O-multiple-picard-flat-proper` (tag 0BF2, Lemma 37.33.6 on the current
web page). The registered source is
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, retained
`more-morphisms.tex`, lines 9613–9619, at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, folder SHA-256
`b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`.
Those lines read: "In this way we see that the trivializing section of
$\mathcal{L}_s$ lifts to a section of $\mathcal{L}$ over $X$. A
straightforward topological argument (omitted) shows that this means that
$\mathcal{L}$ is trivial after possibly shrinking $S$ a bit further." The
proof of the preceding lemma `lemma-H1-O-picard-flat-proper` (tag 0BF1) ends
with the same sentences (lines 9512–9515).

The source first lifts a fibre trivialization to a section and then omits the
argument for making it a trivialization after shrinking the base. This
statement begins with that actual lifted section already given, as the
morphism `φ`; "the lift restricts to the trivializing section of
$\mathcal{L}_s$" is translated as invertibility of the pullback of `φ` to the
fibre, and "$\mathcal{L}$ is trivial after shrinking $S$" as invertibility of
the pullback of the same `φ` to `X ×_S U`. The source's setting (flat proper
morphisms of finite presentation as in tag 0BDP, with its cohomological
hypotheses) is not used. This statement does not construct the lift and does
not claim local triviality from fibrewise triviality of a line bundle alone.

The name refers to its intended application to proper morphisms. Its explicit
assumption is the weaker property `UniversallyClosed f`; properness implies it.
The generalization is internal, supported by the following proof route rather
than asserted to be the literal statement of 0BF2. The locus `W` where `φ` is
an isomorphism on stalks is open for a line bundle. The published pullback
stalk comparison puts the entire fibre above `s` in `W`. Since `f` is closed,
the complement of `f(X \ W)` is an open neighbourhood of `s`. Pullback to
that neighbourhood has invertible stalk maps everywhere, hence is an
isomorphism.

Existing Library interfaces for a proof are
`Langlands.SchemeModule.isOpen_lineBundle_stalkFrame`,
`Langlands.SchemeModule.sectionHomEquiv`,
`Langlands.SchemeModule.pullback_stalk_isIso_iff`, and
`Langlands.SchemeModule.isIso_iff_stalk_isIso`. This module introduces no
new geometric definitions and assumes none of those comparison results as
additional hypotheses.

## Errata check

The retained source folder contains no comment page for tag 0BF2. The current
tag page <https://stacks.math.columbia.edu/tag/0BF2>, fetched 2026-10-30 and
registered as `stacks-tag-0bf2-comments-2026-10-30` (SHA-256
`6c79190af01f0184858fb551214b2c3b3a7c75efc987f0929247950ecb98fe0f`), shows
the same text for the cited lines and "Comments (0)", so no correction affects
this step.
