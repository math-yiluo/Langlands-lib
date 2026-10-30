# Local lifting of a fibre frame detected by two restrictions

Authors: Worker 513 designed and compiled the Lean statement and the first
version of this note. Worker 950 rechecked it against the source and revised
this note.

`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement.{u}` is a
`Prop`-valued definition. It is an intermediate step in the proof of the
Stacks Project, tag 0BF2, specialized to two closed immersions of smooth
proper geometrically connected families. This module states the proposition
and supplies no proof. A separate exact-target proof is still required.

## Exact interface

The only external parameter is the universe `u`. Inside the proposition the
following data are quantified, in this order.

- An arbitrary scheme `S : Scheme.{u}`. It is not assumed reduced,
  noetherian, affine, quasi-compact or quasi-separated.
- Three objects `X X₁ X₂ : Over S`, that is schemes `X.left`, `X₁.left`,
  `X₂.left` with structure morphisms `X.hom`, `X₁.hom`, `X₂.hom` to `S`. Each
  structure morphism is assumed `Smooth`, `IsProper` and
  `GeometricallyConnected` (Mathlib's properties of scheme morphisms). No
  projectivity or cohomological hypothesis is assumed.
- Morphisms `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` in `Over S`, so that
  `iₖ.left ≫ X.hom = Xₖ.hom`, whose underlying scheme morphisms `iₖ.left`
  satisfy `IsClosedImmersion`.
- A line bundle `L : LineBundle X.left` (a locally free rank-one actual
  `𝒪_X`-module, the Library's `IsLocallyFreeRankOne`) and a point `s : S`.

There are three triviality hypotheses, each the existence of an isomorphism
of actual module sheaves with the structure sheaf
`Langlands.Scheme.Modules.structureSheaf`:

- `(Scheme.Modules.pullback i₁.left).obj L.obj ≅ 𝒪_{X₁}` on all of `X₁.left`;
- `(Scheme.Modules.pullback i₂.left).obj L.obj ≅ 𝒪_{X₂}` on all of `X₂.left`;
- `(Scheme.Modules.pullback (X.hom.fiberι s)).obj L.obj ≅ 𝒪_{X_s}`, where
  `X_s = X.hom.fiber s` is Mathlib's scheme-theoretic fibre
  `X ×_S Spec κ(s)` and `X.hom.fiberι s : X_s ⟶ X.left` its projection.

The proposition then introduces the following local definitions.

- `j₁ : X₁.hom.fiber s ⟶ X.hom.fiber s` is
  `pullback.lift (X₁.hom.fiberι s ≫ i₁.left) (X₁.hom.fiberToSpecResidueField s)`,
  the morphism of fibres induced by `i₁.left` through the universal property
  of the fibre product `X_s`; its compatibility uses `Over.w i₁` and
  `X₁.hom.fiber_fac s`. The morphism `j₂` is defined in the same way from
  `i₂`. They are the base changes of `iₖ.left` to `Spec κ(s)`.
- `O = Langlands.Scheme.Modules.structureSheaf (X.hom.fiber s)`, the
  structure sheaf of `X_s` as a module over itself.
- `H = DerivedSections.relativeCohomology (X.hom.fiberToSpecResidueField s) 1`,
  a functor `(X.hom.fiber s).Modules ⥤ ModuleCat κ(s)`. It is the Library's
  first right-derived functor of `κ(s)`-module global sections (pushforward
  to `Spec κ(s)` followed by global sections), computed from chosen
  injective resolutions in `(X.hom.fiber s).Modules`. Thus `H.obj O` is the
  `κ(s)`-module `H¹(X_s, 𝒪_{X_s})`.

The last hypothesis is the degree-one detection condition: every
`c : H.obj O` such that

```text
(H.map ((Scheme.Modules.pullbackPushforwardAdjunction j₁).unit.app O)).hom c = 0
(H.map ((Scheme.Modules.pullbackPushforwardAdjunction j₂).unit.app O)).hom c = 0
```

is zero. Here `(Scheme.Modules.pullbackPushforwardAdjunction jₖ).unit.app O`
is the unit `O ⟶ (jₖ)_* jₖ^* O` of Mathlib's adjunction
`Scheme.Modules.pullback jₖ ⊣ Scheme.Modules.pushforward jₖ`. Equivalently,
the `κ(s)`-linear map

```text
H¹(X_s, 𝒪) ⟶ H¹(X_s, (j₁)_* j₁^* 𝒪) × H¹(X_s, (j₂)_* j₂^* 𝒪)
```

is injective. This is the same adjunction-unit formulation as in the
published `FieldTwoAxisH1InjectivityStatement`.

The conclusion: there exist an open `U : S.Opens`, a proof `hs : s ∈ U`, and
an actual module morphism

```text
σ : 𝒪_{X ×_S U} ⟶ (pullback.fst X.hom U.ι)^* L
```

on `pullback X.hom U.ι`, the base change of `X` along the open immersion
`U.ι`, such that the pullback of `σ` along
`(pullback.snd X.hom U.ι).fiberι ⟨s, hs⟩` is an isomorphism. That map is
the inclusion of the scheme-theoretic fibre of
`pullback.snd X.hom U.ι : X ×_S U ⟶ U` over the point `⟨s, hs⟩` of `U`.
So `σ` is a section of `L` over `X ×_S U` that is a frame on the fibre over
`s`.

The conclusion does not say that `σ` is an isomorphism on all of
`X ×_S U`, nor that its fibre pullback is a preselected frame of `L` on
`X_s`. The hypothesis on `X_s` asks only that some frame exists.

## Source

The Stacks Project, More on Morphisms, Section "Theorem of the cube",
Lemma `lemma-H1-O-multiple-picard-flat-proper`, tag 0BF2. Registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`: the TeX file
`more-morphisms.tex` at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`,
folder SHA-256
`b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`. The
retained `tags.txt` maps 0BF2 to this label, 0BF1 to
`lemma-H1-O-picard-flat-proper` and 0BDP to
`lemma-diagonal-picard-flat-proper`.

- Hypotheses of 0BDP, lines 9198–9215: `f` flat, proper, of finite
  presentation, and `𝒪_T ⟶ p_*𝒪_{X_T}` an isomorphism for every base change
  `T ⟶ S`. The immersion `Z ⟶ S` is characterized by: `T ⟶ S` factors
  through `Z` if and only if the pullback of the given bundle to `X_T` is the
  pullback of a finite locally free module on `T`.
- The single-restriction lemma 0BF1, lines 9429–9516, and its proof.
- The statement of 0BF2, lines 9518–9541, and its complete proof, lines
  9543–9619.

The retained tag page of 0BDP has two comments, a notation typo and a
missing space, both reported fixed in 2025. The live tag pages of 0BF2 and
0BF1, checked on 2026-10-30, have no comments. The Library has no project
errata note on these tags.

### How the statement specializes the source

In 0BF2 take `n = 2`, the diagrams `X₁ ⟶ X` and `X₂ ⟶ X` given by
`i₁.left` and `i₂.left`, and `𝓛 = L.obj`.

- The source assumes that `f` and the `fᵢ` satisfy the hypotheses of 0BDP.
  Here smoothness gives flatness and local finite presentation, and
  properness gives finite type and separatedness, hence quasi-compactness
  and quasi-separatedness, so the morphisms are of finite presentation.
  Smoothness, properness and geometric connectedness are stable under base
  change, and the published
  `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` applied
  to each base change gives that `𝒪_T ⟶ p_*𝒪_{X_T}` is an isomorphism. These
  facts must be proved when the source argument is formalized; they are not
  hypotheses of this proposition.
- Since `𝓛ᵢ = iᵢ^* 𝓛` is isomorphic to `𝒪_{Xᵢ}` on all of `Xᵢ`, every
  `T ⟶ S` factors through `Zᵢ` (take `𝒩 = 𝒪_T`), so `Zᵢ = S`. The proof's
  first reductions, replacing `S` by the scheme-theoretic intersection of
  the `Zᵢ` and shrinking until `𝓛ᵢ = 𝒪_{Xᵢ}`, are therefore not needed.
- Since `𝓛` restricted to `X_s` is trivial, `Spec κ(s) ⟶ S` factors through
  `Z` (take `𝒩 = κ(s)`), so `s ∈ Z`, as the source requires.
- The source's hypothesis is injectivity of
  `H¹(X_s, 𝒪) ⟶ H¹(X_{1,s}, 𝒪) ⊕ H¹(X_{2,s}, 𝒪)`, given by pullback along
  the maps of fibres `jₖ`. The Lean hypothesis uses instead the unit maps
  into `H¹(X_s, (jₖ)_* jₖ^* 𝒪)`. Pullback in cohomology factors through this
  unit map followed by the comparison
  `H¹(X_s, (jₖ)_* jₖ^* 𝒪) ⟶ H¹(X_{k,s}, jₖ^* 𝒪)`, and `jₖ^* 𝒪 ≅ 𝒪`. Since
  `jₖ` is a closed immersion, this comparison is an isomorphism by
  acyclicity of the direct image, and the two hypotheses then agree. That
  comparison must be proved; it is not a hypothesis or data field of this
  proposition.
- The proof of 0BF2 shows, after shrinking `S` to an affine open
  neighbourhood of `s`, that "the trivializing section of `𝓛_s` lifts to a
  section of `𝓛` over `X`" (lines 9615–9616). The conclusion of this proposition is
  that sentence: such a section is a morphism `σ` as above whose restriction
  to the fibre over `s` is a trivializing section, so its fibre pullback is
  an isomorphism. The proposition stops before the final step of the proof,
  the omitted topological argument that `𝓛` becomes trivial after shrinking
  `S` further, and before the identification `Z ∩ U = (Z₁ ∩ Z₂) ∩ U` asserted
  by the lemma.

The statement is therefore derived from the source rather than quoted from
it: it is an intermediate conclusion of the proof of 0BF2 in the special
case above.

## Proof obligations

An exact proof must, following the source, combine: perfect representatives
of `Rf_* 𝓛` and `Rfₖ_* 𝒪` whose formation commutes with arbitrary base
change; local minimal finite free models of these complexes near `s`; actual
derived restriction maps between them compatible with base change; the
degree-zero comparison with the structure sheaf; the combined degree-one
injection, together with the closed-immersion direct-image comparison
above; splitting of the resulting finite matrix after shrinking; and the
comparison of degree-zero sections of the model with actual sections of
`L`. Objectwise derived isomorphisms alone do not identify these maps or
their degree-zero sections. This proposition does not take any of these
constructions as a hypothesis.
