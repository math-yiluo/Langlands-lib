# Proper spreading of an actual line-bundle frame

The theorem
`Langlands.AlgebraicGeometry.Modules.properLineBundleMorphismSpread.{u}`
proves the published proposition
`Langlands.AlgebraicGeometry.Modules.ProperLineBundleMorphismSpreadStatement.{u}`
from the module of the same name. Its type is exactly that proposition, with
an arbitrary universe `u` and no further hypotheses.

## Statement proved

Let `X S : Scheme.{u}`, let `f : X ⟶ S` be universally closed, let
`L : LineBundle X` be a Library line bundle (a locally free rank-one module
sheaf), let `φ : structureSheaf X ⟶ L.obj` be a morphism of module sheaves out
of the structure sheaf, and let `s : S`. If the pullback of `φ` along Mathlib's
first projection `f.fiberι s : f.fiber s ⟶ X` from the scheme-theoretic fibre
is an isomorphism, then there is an open `U : S.Opens` with `s ∈ U` such that
the pullback of the same `φ` along `pullback.fst f U.ι : X ×_S U ⟶ X` is an
isomorphism. Both pullbacks are Mathlib's `Scheme.Modules.pullback` functors
and both isomorphisms are in the actual categories of module sheaves.

## Proof implemented in Lean

Write `φ_x` for the stalk map of `φ` at a point `x : X`, that is, the stalk
functor `TopCat.Presheaf.stalkFunctor Ab x` applied to the underlying presheaf
morphism `(Scheme.Modules.toPresheaf X).map φ`.

1. **The frame locus is open.** Let `σ := (sectionHomEquiv L.obj).symm φ` be
   the global section of `L.obj` corresponding to `φ`, so that
   `sectionHom L.obj σ = φ` (`Langlands.SchemeModule.sectionHomEquiv`, module
   `Langlands.AlgebraicGeometry.Modules.TensorSections`). Let
   `W := {x : X | IsIso φ_x}`. Unfolding
   `Langlands.SchemeModule.IsStalkFrame` and rewriting with
   `sectionHom L.obj σ = φ`, the set `W` is the set in
   `Langlands.SchemeModule.isOpen_lineBundle_stalkFrame L σ` (module
   `Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen`), so `W` is open.

2. **The fibre lies in `W`.** Let `x ∈ f ⁻¹' {s}`. By Mathlib's
   `Scheme.Hom.range_fiberι`, `x = f.fiberι s y` for some point `y` of the
   fibre. Because the pullback of `φ` to the fibre is an isomorphism, its
   stalk map at `y` is an isomorphism (functors preserve isomorphisms). The
   Library comparison `Langlands.SchemeModule.pullback_stalk_isIso_iff`
   (module `Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof`),
   applied to `f.fiberι s`, the locally-free-rank-one property `L.property`,
   `φ` and `y`, says that this holds exactly when `φ_{f.fiberι s y}` is an
   isomorphism. Hence `x ∈ W`.

3. **The neighbourhood.** Since `f` is universally closed, it is a closed map
   (Mathlib's `Scheme.Hom.isClosedMap`). The complement `Wᶜ` is closed, so
   `f '' Wᶜ` is closed and `U := (f '' Wᶜ)ᶜ` is an open subset of `S`. If
   `s ∉ U`, then `s = f x` with `x ∉ W`; but then `x ∈ f ⁻¹' {s} ⊆ W` by
   step 2, a contradiction. So `s ∈ U`.

4. **Every stalk of the base change is invertible.** By
   `Langlands.SchemeModule.isIso_iff_stalk_isIso` (module
   `Langlands.AlgebraicGeometry.Modules.SectionLocusComparison`), it suffices
   that for each point `y` of `X ×_S U` the stalk map at `y` of the pullback of
   `φ` along `pullback.fst f U.ι` is an isomorphism. By
   `pullback_stalk_isIso_iff` applied to `pullback.fst f U.ι`, it suffices that
   `pullback.fst f U.ι y ∈ W`. Suppose not. The point `pullback.snd f U.ι y`
   of the open subscheme `U` maps into `U` under `U.ι`, and the pullback square
   `pullback.condition` gives
   `f (pullback.fst f U.ι y) = U.ι (pullback.snd f U.ι y)`. Hence
   `U.ι (pullback.snd f U.ι y)` lies in `f '' Wᶜ`, contradicting the definition
   of `U`. So every stalk map is invertible and the pullback of `φ` to
   `X ×_S U` is an isomorphism.

The proof uses no hypothesis on `f` beyond universal closedness, no condition
on `L` beyond its being a Library line bundle, and the conclusion is about the
pullback of the given `φ` itself to the full base change `X ×_S U`, including
nilpotents. The file sets `backward.isDefEq.respectTransparency false`, a
definitional-unfolding option of the elaborator; it adds no axiom or
hypothesis. Lean reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The target statement is a derived internal statement isolating the omitted
"straightforward topological argument" at the end of the proof of the Stacks
Project's Lemma 37.33.6 (tag 0BF2), registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, `more-morphisms.tex`,
lines 9613–9619, at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, as
explained in the statement's Markdown. The argument above is one way to supply
that omitted step; it follows the route suggested in the proof task and was
first drafted by Worker 1017.
