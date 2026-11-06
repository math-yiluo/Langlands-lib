# The exponent cone condition for induced representations from a glued geometric lemma

Fix a nonarchimedean local field `k`, a smooth group scheme `G` over `k`, locally
of finite type, with the canonical topology on `G(k)`, and represented parabolics
`P = M N` and `Q = L U` of `G`. The represented geometric lemma
(`Langlands/Representation/Geometric/RepresentedGeometricLemmaStatement.lean`)
writes `r_Q ∘ i_P` as glued from the pieces of intersection data
`D i : GeometricLemmaIntersectionDatum … (z i)`. Each `D i` provides a parabolic
`P'_i = M'_i N'_i` of `M` and a parabolic `Q'_i = L'_i U'_i` of `L`.

This internal supporting module proves the cone half of Renard VII.2.2 for one
parabolic `Q`, with the glued data and three further inputs as explicit
hypotheses.

## Declaration

`Langlands.Aubert.General.RepresentedParabolic.normalizedRealPart_mem_nonnegCone_of_isGluedFrom`.
Its hypotheses are:

- `D : ∀ i, GeometricLemmaIntersectionDatum p l r … q lQ rQ … (z i)` for some
  `z : Fin m → G(k)`, and `hD`: `leviJacquetInductionFunctor` (the composite
  `r_Q ∘ i_P` with values in representations of `L(k)`) is glued (`IsGluedFrom`)
  from the functors `(D i).pieceFunctor`;
- a split component `a : A → L` (`IsSplitComponent a`) and a parabolic root
  presentation `pres` of `(q, lQ, a)`;
- `hneg`: the relative roots of the maximal split torus `pres.data.i` of `G` are
  closed under negation.

Under these hypotheses, let `σ` be a smooth representation of `M(k)` (canonical
topology) with

- `σ` tempered in the published sense `IsNormalizedExponentTempered` for the
  connected reductive group `M`, and
- for every `i`, the Jacquet module of `σ` along `P'_i`
  (`leviJacquetFunctor (D i).p' (D i).l' (D i).r' …`), a representation of
  `M'_i(k)`, admissible.

Then for every `χ : A(k) →* ℂˣ` that is a normalized Jacquet exponent
(`IsNormalizedJacquetExponent q lQ rQ … ha`) of the induced representation
`leviInductionFunctor p l r … σ` along `Q`, its normalized real part
`normalizedRealPart χ` lies in `pres.nonnegCone`.

## Proof

1. `isNormalizedJacquetExponent_iff_leviJacquet` (in
   `GeometricLemmaExponentTransfer.lean`) turns the hypothesis on `χ` into a
   generalized eigencharacter of `leviJacquetInductionFunctor.obj σ` restricted
   along the points of `a`.
2. `IsGluedFrom.exists_isGeneralizedEigencharacter` gives an index `i` such that
   `χ` is a generalized eigencharacter of `(D i).pieceFunctor.obj σ` restricted
   along the points of `a`.
3. `exists_isSplitComponent_factor` (in `GeometricLemmaSplitComponent.lean`) gives
   a split component `a' : A' → L'_i` and `f : A → A'` with
   `f ≫ a' ≫ (L'_i → L) = a`.
4. `exists_isNormalizedJacquetExponent_of_piece` (in
   `GeometricLemmaExponentTransfer.lean`), with the Jacquet admissibility
   hypothesis for `i`, gives `ψ : A'(k) →* ℂˣ` that is a normalized Jacquet
   exponent of `σ` along `P'_i` for the split component `a' ≫ φ.hom` of `M'_i`,
   with `ψ ∘ f = χ` on points.
5. Temperedness of `σ`, applied through `IsNormalizedExponentTempered.parabolic`
   to `(p', l', a' ≫ φ.hom)` (a split component by `IsSplitComponent.comp_iso`),
   gives a presentation `presM` of that triple (the first component of the cone
   condition). The second component, for the radical `r'`, puts
   `normalizedRealPart ψ` in `presM.nonnegCone`.
6. The kernel of `ψ` is open, by the first part of
   `isNormalizedJacquetExponent_iff_isOpen_ker_and`. So the published
   `normalizedRealPart_comp_points` (`Plancherel/SplitTorusRealPartLaws.lean`)
   rewrites `normalizedRealPart χ = normalizedRealPart (ψ ∘ f)` as the real
   restriction along `f` of `normalizedRealPart ψ`.
7. `restrictReal_mem_nonnegCone` (in `RadicalWeightTransfer.lean`), with `hneg`,
   maps `presM.nonnegCone` into `pres.nonnegCone` under that restriction.

## Provenance and scope

This is derived content for the proof of Renard VII.2.2
(`LeviInductionNormalizedTemperedStatement`; Renard, *Représentations des
groupes réductifs p-adiques*, VII.2.2, PDF pp.233–234). Renard proves the cone
condition for `i_P σ` along `Q` by the geometric lemma VI.5.1: an exponent of
`A_L` on `r_Q i_P σ` comes from one of the pieces, by VII.1.1 it restricts from
an exponent of `σ` along a parabolic of `M`, and temperedness of `σ` together
with a Weyl-group comparison places it in the cone of `Q`. The module follows
this route. The Weyl-group comparison is replaced by the weights on the
unipotent radicals (`RadicalWeightTransfer.lean`).

The module does not prove the geometric lemma, the negation closure `hneg`, or
the admissibility of the Jacquet modules of `σ`. They are hypotheses. It also
does not treat the admissibility of `i_P σ` or the existence of presentations
for `Q`, which the full temperedness predicate also requires.
