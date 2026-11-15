# Step 2b of Murre's induction: descent from the completion (proof)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompletionDescentProof`
proves

```
theorem murreCompletionDescent : MurreCompletionDescentStatement.{u, v}
```

(namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor`). The statement is the
published `MurreCompletionDescentStatement` of `MurreLocalStepParts.md`, Step 2b of
Case I of Murre's proof (Bourbaki exp. 294, Proposition 1). Let `R` be a local
noetherian ring with completion `R̂ = AdicCompletion (maximalIdeal R) R`, and let `F` on
`Over (Spec R)` satisfy `MurreConditions F`. If the base changes of `F` to the
punctured spectrum `U = Spec R − {closed point}` and to `Spec R̂` are represented by
separated, locally of finite type, formally unramified schemes, then so is `F`. The proof
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The route differs from Murre's. It does not spread out from `R̂` to finitely generated
subalgebras. Instead it descends quasi-affine charts of `X'` along the faithfully flat
morphism `Spec R̂ ⟶ Spec R` and glues them with the published Murre Lemma 3
(`ChartGluing.murreChartGluing`). The hypothesis over the punctured spectrum is what
makes these charts stable under the descent datum.

## Supporting modules

All helper modules are in the directory `UnramifiedFunctor/CompletionDescent/`, under the
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`. Each has
its own Markdown:

- `QuasiAffine`: effective descent of quasi-affine schemes along a flat surjection of
  affine schemes.
- `Points`: the elements `pt` of `F` defined by morphisms to `X'`, and the descent datum
  `σ` (`exists_sigma`).
- `Puncture`: the comparison morphism `puncMap : X' ×_{Spec R̂} π⁻¹(U) ⟶ X_U`.
- `ChartDatum`: the descent datum on a saturated open of `X'` and its descent.
- `ChartProperties`: the descended element `ξ` is a monomorphism, infinitesimally
  étale and locally of finite type, and it receives every point whose morphism lands in
  the chart.
- `Completion`: `Spec R̂ ⟶ Spec R` is flat, surjective and quasi-compact, and
  field-valued points over the closed point are detected in `Spec R`.
- `Saturation`: the opens `O' ∪ puncι(puncMap⁻¹ M)` are saturated and quasi-compact,
  and they absorb every compact subset.

The proof module also imports the published modules `MurreLocalStepParts` (the
statement), `ChartGluingRepr` (`ChartGluing.murreChartGluing`),
`MurreLocalToGlobalReduction` (`LocalToGlobal.representableByBaseChange`),
`Descent.LocallyQuasiFiniteDescent.QuasiAffineChart`
(`LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite`, a consequence of
Zariski's main theorem) and `Deformation.AdicCompletionNoetherian` (the instance that
`R̂` is noetherian). From Mathlib it imports `Mathlib.RingTheory.Unramified.LocalStructure`.

## Auxiliary lemmas

- `GenericFiniteness.locallyQuasiFinite_of_formallyUnramified`, reused from
  `Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness`: a formally unramified
  morphism locally of finite type is locally quasi-finite. On affine opens, the ring
  map is formally unramified and of finite type, hence quasi-finite.
- `isSeparated_of_isSeparated_pullback_snd`: let `π` be flat, surjective and
  quasi-compact. If the base change `Y ×_S S' ⟶ S'` of `q : Y ⟶ S` is separated, then
  `q` is separated. Proof: the diagonal of the base change is universally closed. The
  property "diagonal universally closed" descends along such `π` (Mathlib's
  `MorphismProperty.diagonal` descent instance), so the diagonal of `q` is universally
  closed, and in particular has closed range. An immersion with closed range is a closed
  immersion (`IsClosedImmersion.of_isPreimmersion`).
- `exists_chart`: let `σ` be the descent datum of `exists_sigma`. Let `F` satisfy
  (F1b), let `q'` be separated, locally of finite type and formally unramified, and let
  `O' : X'.Opens` and `M : X_U.Opens` be compact with `puncMap(puncι⁻¹ O') ⊆ M`. Then
  there are `w : V ⟶ Spec R` locally of finite type and `ξ ∈ F(V)`, a monomorphism that
  is infinitesimally étale at every point, with the following property. Every
  `v ∈ F(T)` whose morphism `v' : T ×_S Spec R̂ ⟶ X'` (with `pt v' = v|_{T ×_S Spec R̂}`)
  lands in `O'` factors as `v = F.map h.op ξ`. Proof: let `W := satOpen O' M`. It is
  saturated (`sat_satOpen`) and compact (`isCompact_satOpen`). Since
  `W ⟶ X' ⟶ Spec R̂` is separated, locally of finite type and locally quasi-finite
  over an affine base, `W` is quasi-affine
  (`LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite`). Then
  `exists_chart_isPullback` gives `V`, `w` and `p`, and `exists_isChartElement` gives
  `ξ`. The properties come from `locallyOfFiniteType_w`,
  `isMonoElement_of_isChartElement`, `infinitesimallyEtaleAt_of_isChartElement` and
  `exists_map_eq_of_range_subset` (as `O' ⊆ W`).

## Proof of `murreCompletionDescent`

Let `π := completionMap R`. Take `e` representing `F ×_S Spec R̂` by
`q' : X' ⟶ Spec R̂` (separated, locally of finite type, formally unramified), and `eU`
representing `F ×_S U` by `qU : X_U ⟶ U`. Let `σ` come from `exists_sigma e`.

1. *Charts.* Let `ι` be the type of pairs `(O', M)` of compact opens of `X'` and `X_U`
   with `puncMap(puncι⁻¹ O') ⊆ M`. This type lies in universe `u`. For each `c : ι`,
   `exists_chart` gives `V c`, `w c` and `ξ c`.
2. *Field points.* Let `K` be a field, `f : Spec K ⟶ Spec R` and `η ∈ F(Spec K)`. Put
   `T := (Spec K, f)`. By `exists_pt` there is `v' : T ×_S Spec R̂ ⟶ X'` over the second
   projection with `pt v' = η|_{T ×_S Spec R̂}`. The scheme `Spec K ×_S Spec R̂` is affine,
   so `range v'` is compact. By `exists_satOpen` (which needs `R̂` noetherian and `q'`
   locally of finite type) it lies in some `O'` with `(O', M) ∈ ι`. Then `exists_chart`
   factors `η` through `ξ (O', M)`.
3. *Gluing.* `ChartGluing.murreChartGluing` applies to `Spec R` (locally noetherian),
   using the conditions `SmallValues`, (F1a), (F1b), (F2), (F3) from
   `MurreConditions F`, the family of step 1 and the covering property of step 2. It
   gives `q : Y ⟶ Spec R` locally of finite type and `e'` representing `F`.
4. *Comparison over `Spec R̂`.* `LocalToGlobal.representableByBaseChange e' π`
   represents `F ×_S Spec R̂` by `Y ×_S Spec R̂ ⟶ Spec R̂`. Uniqueness of representing
   objects (`RepresentableBy.uniqueUpToIso` against `e`) gives an isomorphism
   `i : Y ×_S Spec R̂ ≅ X'` over `Spec R̂`, so `pullback.snd q π = i ≫ q'`.
5. *Separatedness.* `i ≫ q'` is separated, so `q` is separated by
   `isSeparated_of_isSeparated_pullback_snd` (with the instances of `Completion`).
6. *Formal unramifiedness.* `i ≫ q'` is formally unramified: an isomorphism is
   formally unramified (Mathlib instance) and the property is stable under composition
   (`MorphismProperty.comp_mem`). Formal unramifiedness descends along flat, surjective,
   quasi-compact morphisms (Mathlib's `LocalFlatDescent` instance), and
   `MorphismProperty.of_isPullback_of_descendsAlong` applied to the pullback square of
   `q` and `π` gives `FormallyUnramified q`.

So `Y`, `q`, `e'` witness `UnramifiedRepresentable F`.

Only the conditions `SmallValues`, (F1a), (F1b), (F2) and (F3) of `MurreConditions F`
are used, together with the separatedness, local finite type and formal
unramifiedness of `X'`. The hypothesis over `U` is used only through the representing
scheme `X_U`, not through its three properties.
