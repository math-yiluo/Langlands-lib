# The chart maps into the glued analytic space

Setting (namespace `Langlands.Analytic.SpaceAnalytification.ChartQuotient`): `K` a complete
ultrametric nontrivially normed field, `X` a separated algebraic space over `Spec K`
(`hX`), a family of affine charts `x i : Spec A_i → X` with finite polynomial presentations
`P i`, and `EtaleHomSheafStatement.{u, u}` (`hSheaf`).

Data and hypotheses:

- `CJ A = Σ i, PrimeSpectrum (A i)`, and for each `j = (i, p)` an elementary chart
  `E j : ElemChart X` (module `SpaceChartQuotientGluing`).
- `CM E`: the pieces, pairs of `j` and a point `v` of `Spec(B_j)ᵃⁿ` with center the
  elementary prime `q_j`. `Nj j` is the chosen model `pointModel` of
  `Spec A_i ×_X Spec B_j`.
- Open sets `O m ⊆ Spec(B_j)ᵃⁿ` (`hO`) on which the relation is trivial (`htriv`, as in
  `chartRelation`); the glued space is `(chartRelation hX E (·.1) O hO htriv hSheaf).glued`.
- `hvO`: `v ∈ O m` for every piece `m = (j, v)`;
  `ha`: for every `j = (i, p)` some prime of the model `Nj j` contracts to `p` and to `q_j`;
  `hOr`: `O m` lies in the image of `Spec(Nj j)ᵃⁿ → Spec(B_j)ᵃⁿ`; `hx`: every `x i` is étale.

Cover of the chart `x i`: indices `CI E i` (a prime `p` of `A_i` and a point `v` over `q_{(i,p)}`);
`Dk i k` is the open domain of `Spec(Nj (i, p))ᵃⁿ` over `O (i, p, v)`; the cover map
`ek i k : Dk i k ⟶ Spec(A_i)ᵃⁿ` and the map `hk i k : Dk i k ⟶ DZ (i, p, v)` to the piece are
the restricted analytified projections, and `φk i k = hk i k ≫ ιL (i, p, v)`.

Results:

- `etale_ek`, `ek_cover` (the cover maps are étale and jointly surjective, using `hvO`, `ha`
  and `exists_baseMap_eq_center`), `mono_ek`, `openImmersion_ek`.
- `rel_hk`: maps into two cover domains whose composites to the charts are related through a
  model of `Spec A_i ×_X Spec A_{i'}` give maps into the pieces related by `chartRelation`.
- `π i : Spec(A_i)ᵃⁿ ⟶ glued` with `ek i k ≫ π i = φk i k` (`ek_π`); `etale_π`;
  `π_surjective` (with `hOr`).
- `π_eq_of_aRel` and `aRel_of_π_eq`: for `α : T ⟶ Spec(A_i)ᵃⁿ`, `β : T ⟶ Spec(A_j)ᵃⁿ` and a
  model `M` of `Spec A_i ×_X Spec A_j`, `α ≫ π i = β ≫ π j` iff `α` and `β` are related
  through `M`.
- `isPullback_π`: for a `K`-algebra `B` with presentation `Q` and maps `f : A_i → B`,
  `g : A_j → B` such that `Spec B = Spec A_i ×_X Spec A_j` (a pullback square of
  presheaves), `IsPullback (localizedHom K (P i) Q f) (localizedHom K (P j) Q g) (π i) (π j)`.
- `etale_of_openImmersion_cover`: a morphism whose composites with a jointly surjective
  family of open immersions are étale is étale.

## Proof

- `rel_hk`: compose the given relation with the relations of the cover maps to the
  elementary charts through `Nj` (symmetry and transitivity, `SpaceChartRelation`) to get a
  relation through `Wm` of the composites into the elementary charts; `exists_of_aRel`
  lifts it to the relation space.
- `mono_ek`: if `l ≫ ek = m ≫ ek`, `rel_hk` with the diagonal relation gives related maps
  into one piece, which are equal (`rel_self_iff`); so `l` and `m` agree after both
  projections of `Nj` and are equal by `jointly_mono`. With `hSheaf`, `ek` is an open
  immersion (`openImmersion_of_etale_of_mono`).
- `ek_cover`: for a point `u` with center `p`, `ha` gives a prime `𝔓` of the model over `p`
  and `q_j`; `exists_baseMap_eq_center` gives a point `w` over `u` with center `𝔓`, whose
  image `v` in `Spec(B_j)ᵃⁿ` has center `q_j`, so `w` lies in `Dk i (p, v)` by `hvO`
  (`mem_range_ek`).
- `π i`: the `φk i k` are compatible on the cover (`φk_compat`: `rel_hk` and `Rel.ιL_eq`), so
  they descend (`exists_glue_of_etale_cover`). Étaleness: on the open images of the open
  immersions `ek i k`, `π i` restricts to the étale maps `φk i k` (`hk` étale, `ιL` an open
  immersion), and `etale_of_openImmersion_cover` applies (via `etale_of_open_source_cover`).
- `π_surjective`: a point of the glued space is `ι m z` for a piece `m = (i, p, v)`; by
  `hOr`, `z` comes from a point `w` of `Spec(Nj)ᵃⁿ`, which lies in `Dk` and maps to `z` under
  `hk` (`exists_hk_eq`), so `ι m z = π i (ek w)`.
- Pullbacks: a test space `T` with maps `α, β` is covered by the open domains `TDom` where
  `α` and `β` factor through cover maps `ek i k`, `ek j k'` (`tcover`, `exists_tlift₁`,
  `exists_tlift₂`). If `α, β` are related, the factors are related by `rel_hk`, so they agree
  after `ιL` (`Rel.ιL_eq`), and `α ≫ π i = β ≫ π j` by `hom_ext_of_etale_cover`. Conversely,
  equal composites make the factors agree after `ιL`, so they lift to the relation space
  (`isPullback_ιL`, `aRel_of_lift`); chaining with the relations through `Nj` gives a relation
  through `M` on each domain, and `ARel.of_etale_cover` globalizes it. `isPullback_π` is
  `isPullback_of_aRel` for the model given by `(B, Q, f, g)`.

## Provenance

Derived. This is the construction of the quotient morphism in Conrad–Temkin,
*Non-archimedean analytification of algebraic spaces* (2009), Lemma 4.2.3 and its proof,
pp.20–21, and Lemma 4.3.1, p.23 (`conrad-temkin-2009-nonarchimedean-analytification`): the
étale composites of the charts with the quotient maps of the local pieces glue by étale
descent of morphisms, the two composites `R ⇉ X` coincide and `R → U ×_X U` is an
isomorphism; here this is stated for the analytified charts `Spec(A_i)ᵃⁿ` and their affine
fibre products. The elementary charts and the relation-trivial pieces replace the
Galois-split charts of Conrad–Temkin, Lemma 4.3.3 (see `SpaceChartTrivialOpen`).
