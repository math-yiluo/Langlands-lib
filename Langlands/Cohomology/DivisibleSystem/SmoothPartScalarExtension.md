# Extension of scalars of the smooth part

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension`
(`smoothRepExtendScalars`, `smoothRepExtendScalarsComplex`), on
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (`repExtendScalars`,
`repExtendScalarsComplex`, `smoothPartComplex`, `smoothPartComplexInclusion`,
`quotientInvariantsInverseLimitBaseChangeSmooth`,
`quotientInvariantsInverseLimitBaseChangeSmoothInclusion` and their
`Completion` forms), on `Langlands.Representation.Category.SmoothPartAdjunction`
(`SmoothRep.smoothPartFunctor`, `SmoothRep.toRepSmoothPartAdjunction`) and on
`Langlands.Cohomology.DivisibleSystem.InverseLimit`
(`quotientInvariantsInverseLimit`). From Mathlib it uses
`Adjunction.homEquiv_naturality_left_square`, `Adjunction.homEquiv_counit`,
`Adjunction.counit_naturality` and `HomologicalComplex.hom_ext`.

Everything is in the namespace `Langlands.Cohomology`. Write `V^sm` for the
smooth part of a representation `V`: the subrepresentation of vectors fixed
by some open subgroup, `SmoothRep.smoothPartFunctor`. It is right adjoint to
the inclusion `SmoothRep.toRep` of smooth representations, with counit the
inclusion `V^sm → V` (`SmoothRep.toRepSmoothPartAdjunction`). For an algebra
`R → S` there are two ways to go from a representation `V` over `R` to a
smooth representation over `S`: `S ⊗[R] V^sm` (smooth part, then extension
of scalars) and `(S ⊗[R] V)^sm` (extension of scalars, then smooth part).
This module defines the canonical map from the first to the second.

## The natural map

`R` and `S` are commutative rings (universes `uR`, `uS`) with an algebra
structure `algebraMap R S`, and `G` is a topological group.

- `smoothPartExtendScalars R S G`: the natural transformation
  `SmoothRep.smoothPartFunctor R G ⋙ smoothRepExtendScalars R S G ⟶
  repExtendScalars R S G ⋙ SmoothRep.smoothPartFunctor S G` of functors
  `Rep.{w} R G ⥤ SmoothRep.{uS, uG, max uS w} S G`. Its component at `V`
  is defined as follows. Extension of scalars of the inclusion `V^sm → V` is
  a map of representations `S ⊗[R] V^sm → S ⊗[R] V`. Its source is
  smooth (the SmoothScalarExtension module), so the adjunction bijection of
  `SmoothRep.toRepSmoothPartAdjunction S G` turns it into a map of smooth
  representations `S ⊗[R] V^sm → (S ⊗[R] V)^sm`. Naturality in `V` follows
  from the naturality of the inclusion `V^sm → V` and of the adjunction
  bijection (`Adjunction.homEquiv_naturality_left_square`).
- `smoothPartExtendScalars_app_tmul R S G V s v`: the component sends
  `s ⊗ v` to `s ⊗ v`, now viewed as a smooth vector of `S ⊗[R] V` (`rfl`).
- `smoothPartExtendScalars_app_comp_counit R S G V`: the component followed
  by the inclusion `(S ⊗[R] V)^sm → S ⊗[R] V` equals the extension of
  scalars of the inclusion `V^sm → V`, as morphisms in `Rep S G`. This is
  `Adjunction.homEquiv_counit` applied to the defining bijection.

## Complexes

`c` is a complex shape on an index type `ι`.

- `smoothPartComplexExtendScalars R S G c`: the natural chain map from
  `smoothPartComplex R G c ⋙ smoothRepExtendScalarsComplex R S G c` to
  `repExtendScalarsComplex R S G c ⋙ smoothPartComplex S G c`, with
  degree-`i` component the component of `smoothPartExtendScalars` at the
  degree-`i` term. It commutes with the differentials, and is natural in the
  complex, by naturality of `smoothPartExtendScalars`.
- `smoothPartComplexExtendScalars_app_comp_inclusion R S G c K`: this chain
  map followed by the degreewise inclusion `smoothPartComplexInclusion S G c`
  of smooth vectors of `S ⊗[R] K` equals the degreewise extension of scalars
  of the inclusion `smoothPartComplexInclusion R G c` of smooth vectors of
  `K`. It is proved degree by degree from the previous section.

## Harris's complex

The variables are those of the Harris section of the ScalarExtension module:
`K` is an `ℓ`-divisible system of `ℕ`-graded complexes in
`SmoothRep.{uR, uG, max w uR uG} R G`, `N : ℕ`, `ι` a filtered preorder with
an antitone family `H` of normal subgroups of finite index (`hH`), and the
hypotheses `hK` (surjectivity on invariants) and `hk` (kernel orders are
units in `R`) of the InverseLimit module. `S` is a commutative `R`-algebra
in the universe `uR` of `R`, and `G` is a topological group.

- `quotientInvariantsInverseLimitSmooth N K H hH hK hk`: the degreewise
  smooth part of `quotientInvariantsInverseLimit N K H hH hK hk`, a
  `ℤ`-graded cochain complex in `SmoothRep R G`.
- `quotientInvariantsInverseLimitSmoothInclusion N K H hH hK hk`: its
  degreewise inclusion into `quotientInvariantsInverseLimit`, the component
  of `smoothPartComplexInclusion`.
- `quotientInvariantsInverseLimitSmoothBaseChange S N K H hH hK hk`: the
  degreewise extension of scalars `S ⊗[R] -` of
  `quotientInvariantsInverseLimitSmooth`, a `ℤ`-graded cochain complex in
  `SmoothRep S G`.
- `quotientInvariantsInverseLimitSmoothBaseChangeMap S N K H hH hK hk`: the
  chain map from `quotientInvariantsInverseLimitSmoothBaseChange` to the
  published `quotientInvariantsInverseLimitBaseChangeSmooth` (extension of
  scalars first, then the smooth part), the component of
  `smoothPartComplexExtendScalars` at `quotientInvariantsInverseLimit`.
- `quotientInvariantsInverseLimitSmoothBaseChangeMap_comp_inclusion`: this
  chain map followed by
  `quotientInvariantsInverseLimitBaseChangeSmoothInclusion` equals the
  degreewise extension of scalars of
  `quotientInvariantsInverseLimitSmoothInclusion`.

## Coefficients at a finite place

As in the ScalarExtension module, `L` is a number field in universe `uR`, `l`
a finite place of `L`, `R = CoefficientIntegers l` (the valuation ring of
the completion) and `S = FiniteCompletion L l`, with Mathlib's inclusion of
the valuation subring into the completion. The other variables are as in the
previous section with `R = CoefficientIntegers l`; `ℓ` is an arbitrary
natural number.

- `quotientInvariantsInverseLimitSmoothCompletion l N K H hH hK hk`:
  `quotientInvariantsInverseLimitSmoothBaseChange` with
  `S = FiniteCompletion L l`, a complex in
  `SmoothRep (FiniteCompletion L l) G`.
- `quotientInvariantsInverseLimitSmoothCompletionMap l N K H hH hK hk`: the
  corresponding chain map to the published
  `quotientInvariantsInverseLimitCompletionSmooth`.
- `quotientInvariantsInverseLimitSmoothCompletionMap_comp_inclusion`: the
  corresponding equation with
  `quotientInvariantsInverseLimitCompletionSmoothInclusion` and the
  extension of scalars of `quotientInvariantsInverseLimitSmoothInclusion`.

The declarations of the last two sections are abbreviations for, or
instances of, the generic constructions applied to
`quotientInvariantsInverseLimit`.

## Provenance and interpretation

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
printed p.92 (one-based PDF page 18), obtains "in the inverse limit over n
[...] a complex of smooth Z_ℓ[S(e,d)]-modules" and continues: "Tensoring
with Q_ℓ, we obtain our complex C(e,d)." Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999),
printed p.311 (one-based PDF page 13), forms `lim 𝓛̃_m ⊗_𝒪 L_ℓ` and works in
"the category of smooth L_ℓ[GJ]-modules" (Proposition 4.10). Both passages
are quoted at more length in the ScalarExtension module's Markdown.

Harris's inverse limit is a complex of smooth modules by Berkovich's
results, so for him the smooth part plays no role. We have not proved that
`quotientInvariantsInverseLimit` has smooth terms, and the published
modules take smooth parts as a device of ours. This leaves two candidate
renderings of Harris's tensored complex in `SmoothRep S G`:
`quotientInvariantsInverseLimitSmoothBaseChange` (smooth part, then
tensoring, the order of Harris's sentence) and the published
`quotientInvariantsInverseLimitBaseChangeSmooth` (tensoring, then smooth
part). This module supplies the canonical chain map from the first to the
second. If the terms of the inverse limit were smooth, all inclusions of
smooth vectors involved would be isomorphisms and so would this map; the
module does not prove this.

The map, its complex version and the equations are ours. The map is the
standard factorization, through the smooth part, of a map out of a smooth
representation. The cited passages do not contain it.

## Scope

The module defines the natural map `S ⊗[R] V^sm → (S ⊗[R] V)^sm`, its
degreewise version on complexes, the equations identifying their composites
with the inclusions of smooth vectors, and their values on
`quotientInvariantsInverseLimit` for a general algebra and for
`CoefficientIntegers l → FiniteCompletion L l`. It does not prove that the
map is injective, surjective, an isomorphism or a quasi-isomorphism, for
any `S` (for example flat or a localization of `R`). It proves nothing about
Ext groups or derived functors, inverse limits, cohomology or the
smoothness of `quotientInvariantsInverseLimit`.

Source registration: Harris 1997, `harris-1997-drinfeld-cohomology`,
SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`;
Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
