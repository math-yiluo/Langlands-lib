# Zariski gluing of actual rigidified abelian-scheme classes

`Langlands.AbelianScheme.rigidifiedClassesZariskiGluing` proves exactly
`Langlands.AbelianScheme.RigidifiedClassesZariskiGluingStatement.{u}`. The
statement is imported unchanged from
[`RigidifiedClassesZariskiGluingStatement`](RigidifiedClassesZariskiGluingStatement.md).
Let `S : Scheme.{u}` be a scheme, `A` an abelian scheme over `S`, `T : Over S`
a test scheme and `𝒰 : T.left.OpenCover.{u}` an open cover. Let `q i` be actual
rigidified classes on the cover members whose `classesPullback` images agree
on every pairwise overlap. Then some actual class `q₀ : RigidifiedClasses A T`
restricts to every `q i`. The theorem has no further hypotheses.

The proof builds an actual rigidified line bundle on `T ×_S A`. It glues the
underlying module sheaves of chosen local representatives, proves that the
glued sheaf is locally free of rank one, glues the rigidification, and
identifies each restriction with its local representative by a rigidified
isomorphism. Passing to classes then gives the conclusion. All of this is the
theorem `rigidifiedClassesZariskiGluing_of_moduleGluing`. It takes general
object gluing of module sheaves,
`Langlands.Scheme.Modules.OpenCoverModuleGluingStatement.{u}`, as its only
argument. The final theorem supplies that argument with the published
unconditional proof `Langlands.Scheme.Modules.openCoverModuleGluing` (module
`Langlands.AlgebraicGeometry.Modules.OpenCoverModuleGluingProof`). The other
main inputs are published theorems, used directly:

- `Langlands.AbelianScheme.rigidifiedIsoUniqueness` (rigidified isomorphisms
  are unique);
- `Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing` (unique
  gluing of module maps);
- `Langlands.Scheme.Modules.openCoverIsoGluing_of_homGluing` (gluing of module
  isomorphisms);
- the helpers of the published
  [`RigidifiedClassesZariskiSeparatedProof`](RigidifiedClassesZariskiSeparatedProof.md),
  in particular `relativeOpenCover`, `square_compatible_of_common_map`,
  `pullback_map_injective_of_iso` and `pullbackCongr_hom_val`.

No gluing, descent or cocycle proposition remains a hypothesis of the final
theorem.

## Generic comparison lemmas

Section `Langlands.Scheme.Modules` adds small facts about actual module
pullbacks. It reuses `compIso` and `compIso_hom` from
[`Modules.PullbackTransport`](../Modules/PullbackTransport.md). The former
packages the published comparison `compHom` for an equal composite as an
isomorphism; the latter is used locally as a simplification rule.
`squarePullbackIso_hom_compHom` composes a square comparison with an
equal-composite comparison. `pullback_map_pullbackUnitIso_hom` computes the
pullback of the unit comparison `pullbackUnitIso` of a composite.

`chartRigidification ε N ci ri` handles a module `N` on `Y`, a base section
`ε : B ⟶ Y` and a chart `Gi : Yi ⟶ Y` over a base piece `fi : Bi ⟶ B`. The
chart has a section `εi` and a commuting square `ci : εi ≫ Gi = fi ≫ ε`. From
a rigidification `ri` of `Gi^* N` along `εi`, it builds the induced
isomorphism `fi^* O_B ≅ fi^* ε^* N`. It is `pullbackUnitIso` followed by `ri`
and the inverse rigidified square comparison.
`chartRigidification_restrict` restricts it further along a second chart. The
restricted isomorphism is the chart rigidification of the pulled-back
rigidified module, up to the canonical comparisons. The proof cancels the
comparisons with `compHom_assoc` and the published
`pullback_rigidification_hom_comp`. `restricted_rigidification_eq` handles two
charts whose restricted rigidified modules are related by a rigidified
morphism `Θ`. If the underlying module map of `Θ` is the square comparison of
`N`, the two restricted rigidifications agree.

## Rigidified comparison isomorphisms

In namespace `RigidifiedLineBundle`, `forgetModule` is the functor from
rigidified line bundles to their underlying module sheaves. `pullbackCompTo`
compares iterated rigidified pullback with pullback along chosen equal
composites. It is built from the published `pullbackComp` and `pullbackCongr`
with `RigidifiedModule.pullbackCoherence`. `squareIso` is the rigidified
comparison between the two orders of pullback around a commuting square. The
lemmas `forgetModule_map_pullbackCompTo_hom` and
`forgetModule_map_squareIso_hom` identify their underlying module maps with
`compHom` and the published module `squarePullbackIso`. Both use
`pullbackCongr_hom_val`.

`rigidifiedIso_subsingleton_of_iso` extends the published uniqueness. Fix a
slice object `V` and an isomorphism `Q` from its relative space to a scheme
`Y`. Over any section of `Y` that `Q` identifies with the relative unit
section, there is at most one isomorphism between two rigidified line bundles.
Pull both isomorphisms back along `Q.hom`, apply `rigidifiedIsoUniqueness` on
`V`, and conclude with `pullback_map_injective_of_iso`.

`over_isPullback` shows that a scheme fiber product of two maps into
`Y.left` is a pullback square in `Over S`. `relativeSection_comp_square` and
`relativeSection_comp_square'` carry the relative unit section through
identifications of relative spaces, by naturality of `relativeSection`.

## Overlaps and the cocycle

Write `𝒱 = relativeOpenCover S A T 𝒰` for the induced cover of `T ×_S A`.
Its members are the relative spaces of the cover members. The published
preservation of pullbacks by the relative-space functor and `over_isPullback`
give `overlapIso`: the relative space of a base overlap is the actual fiber
product of two members of `𝒱`. `overlapSection` is the relative unit section
of the base overlap followed by this isomorphism. `tripleIso` and
`tripleSection` do the same for the canonical triple overlap
`pullback (pullback.fst uᵢ uⱼ) (pullback.fst uᵢ uₖ)`, using
`IsPullback.of_iso`. `tripleLift` is the lift to the overlap of `j` and `k`
used in the gluing statement, and `tripleSection_lift` makes it compatible
with the unit sections. `isoTransport` and `overlapRigidIso` transport a
rigidified isomorphism over the base overlap to the overlap of `𝒱`, with the
section `overlapSection`. They compose with `pullbackCompTo` on both sides.

`exists_glued` applies the module-gluing statement to `𝒱`. The local modules
are the carriers of the representatives `L i`. The overlap isomorphisms are
the underlying module maps `forgetModule` of the transported isomorphisms.
For the cocycle condition at `i, j, k`, both sides are underlying maps of
rigidified isomorphisms on the triple overlap: `α` composes the two pulled-back
transition isomorphisms with two `squareIso` comparisons, and `β` composes
one `squareIso` with the third. `rigidifiedIso_subsingleton_of_iso`, applied
with `tripleIso`, gives `α = β`. Applying `forgetModule` and simplifying with
`forgetModule_map_pullback_map` and `forgetModule_map_squareIso_hom` yields
exactly the cocycle equation of the statement. The result is a module sheaf
`N` on `T ×_S A` with isomorphisms `ψ i` to the local carriers. They are
compatible with the transported overlap isomorphisms.

## The glued rigidified line bundle

`IsLocallyFreeRankOne.exists_of_pullback` handles an open immersion `g`. If
`g^* M` is locally free of rank one, then near each point of the image of `g`
some open restriction of `M` is isomorphic to the unit module. The chart
`V.ι ≫ g` is identified with its image `opensRange` by `isoOpensRange`. The
identifications use Mathlib's `restrictFunctorIsoPullback`, `pullbackId`,
`compIso` and `pullbackUnitIso`. `glued_isLocallyFreeRankOne` combines this
with `Cover.exists_eq` for `𝒱` and the isomorphisms `ψ i`. Hence `N` is
locally free of rank one.

`chartComm` is the base-section square of a cover member. `chartRig` moves
the rigidification of `L i` to `𝒱.f i ^* N` along `ψ i`. Then `chartRigIso`
is `ψ i` as a rigidified isomorphism. `exists_rigidification` glues the chart
rigidifications to a global isomorphism `ρ : O_T ≅ ε^* N`, where `ε` is the
relative unit section of `T`. It applies `openCoverIsoGluing_of_homGluing`
with the published `openCoverHomGluing` on the base cover `𝒰`, to the chart
rigidifications. On an overlap, `chartRigidification_restrict` restricts both
chart rigidifications. The rigidified map `Θ'` conjugates the transported
transition isomorphism by `chartRigIso`. By the compatibility of `ψ` it has
the square comparison of `N` as underlying map. So
`restricted_rigidification_eq` identifies the two restricted rigidifications,
and `square_compatible_of_common_map` gives the overlap compatibility
required by isomorphism gluing.

`glued_restrict_iso` shows that the relative pullback of the rigidified
family `⟨⟨N, ρ⟩, hN⟩` to member `i` is isomorphic to `L i`, by
`RigidifiedLineBundle.isoMk` with the module isomorphism `ψ i`. The required
rigidification equation follows from the restriction formula for `ρ` after
cancelling the unit and square comparisons.

## Passing to classes

`rigidifiedClassesZariskiGluing_of_moduleGluing` chooses representatives
`(q i).out`. After rewriting with `Quotient.out_eq`, `Quotient.exact` turns
each overlap equality of classes into `Nonempty` of the actual rigidified
isomorphism between the relative pullbacks. Classical choice selects these
transitions. The preceding lemmas give `N`, `ψ`, local freeness and `ρ`. The
global class is the class of `⟨⟨N, ρ⟩, hN⟩`. For each `i`, `Quotient.sound`
applied to `glued_restrict_iso`, followed by `Quotient.out_eq`, proves that
it restricts to `q i`. The final theorem `rigidifiedClassesZariskiGluing`
instantiates this with `Langlands.Scheme.Modules.openCoverModuleGluing`.

## Provenance and scope

This is an internal proof of the published derived statement. The source
context is recorded in the statement's paired Markdown: Edixhoven, van der
Geer and Moonen, *Abelian Varieties*, preliminary draft, Chapter VI §1,
(6.2)(iii). That source derives the sheaf property from descent of line
bundles; this module makes no further literature assertion. The proof follows
the route of the task: choose representatives, take overlap isomorphisms,
prove the cocycle condition by rigidity, glue modules, check local freeness,
glue the rigidification and identify the restrictions. Module gluing is
Stacks Project, Section 6.33 (tag 00AK), Lemmas 6.33.2 and 6.33.3. It is
stated and proved separately, and this proof uses it only through its
published Lean statement and proof.

The universes, schemes and covers are those of the target throughout. Bases
and tests may be nonreduced or non-quasi-separated, and covers may be infinite
and non-affine. No affineness, finiteness, quasi-separatedness,
representability, universal-family, class-sheaf, automorphism-rigidity,
global-functions or cocycle assumption is introduced. The theorem asserts
existence of a glued class only; uniqueness is the separate published
`rigidifiedClassesZariskiSeparated`.
