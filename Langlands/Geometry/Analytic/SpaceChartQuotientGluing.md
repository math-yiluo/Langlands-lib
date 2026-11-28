# Gluing data from relation-trivial open subsets of elementary charts

Let `K` be a complete ultrametric nontrivially normed field and `X` a separated algebraic
space over `Spec K` (`hX : IsSeparated X`).

`ChartQuotient.ElemChart X` (namespace `Langlands.Analytic.SpaceAnalytification`) bundles an
étale affine chart of `X` elementary at a prime: a `K`-algebra `B` with a finite polynomial
presentation `Q`, an étale point `y : Spec B → X`, a prime `q` of `B`, and the elementary
property: for every affine model `Spec C = Spec B ×_X Spec B` with projections `f g : B → C`
and every `μ : C → B` with `μ ∘ f = id = μ ∘ g`, the only prime of `C` contracting to `q`
along both `f` and `g` is `μ⁻¹(q)`.

`ElemChart.exists_trivial_open`: for an elementary chart `E` and a point `v` of `Spec(B)ᵃⁿ`
with center `q`, there is an open `O ∋ v` such that maps `α, β : T ⟶ Spec(B)ᵃⁿ` with image in
`O` that are related through the chosen model `pointModel hX E.Q E.Q E.y E.y` of
`Spec B ×_X Spec B` are equal.

Gluing data. Let `E : J → ElemChart X`, `c : M → J` (the chart of each piece) and open sets
`O m ⊆ Spec(B_{c m})ᵃⁿ`. For pieces `m, n` let `Wm m n` be the chosen model of
`Spec B_{c m} ×_X Spec B_{c n}` with analytified projections `p₁`, `p₂`. The open domains are
`DZ m` (on `O m`) and `DS m n` (on `SSet m n = p₁⁻¹(O m) ∩ p₂⁻¹(O n)`), with the restricted
projections `aM m n : DS m n ⟶ DZ m` and `bM m n : DS m n ⟶ DZ n`. Assume the relation is
trivial on every `O m` (`htriv`: maps into `O m` related through `Wm m m` are equal) and
assume `EtaleHomSheafStatement.{u, u}`. Then `chartRelation` is the gluing data
`LocalizedOpenRelation K` with pieces `Z m = DZ m`, relation spaces `S m n = DS m n` and
projections `aM`, `bM`.

The module also proves `etale_aM`, `etale_bM`, `mono_aM`, `mono_bM`, `exists_of_aRel` (maps
into two pieces whose composites to the charts are related through `Wm m n` factor through
`DS m n`) and `aRel_of_lift` (the converse).

## Proof

- `ElemChart.exists_trivial_open`: separatedness gives a model of `Spec B ×_X Spec B` closed
  in `Spec B ×_K Spec B` (`hasClosedAffinePointPullbacks_of_isSeparated`); apply
  `exists_trivial_open` (module `SpaceChartTrivialOpen`) to it and transfer the relation to
  the chosen model (`ARel.of_model`).
- `aM m n` followed by the inclusion of `DZ m` equals the inclusion of `DS m n` followed
  by `p₁`. For `bM m n` the corresponding equation uses the inclusion of `DZ n` and `p₂`.
  Since both projections are analytifications of étale algebra maps, the equations give
  `etale_aM` and `etale_bM` by `etale_of_comp_domainι`.
- `mono_aM`: if `s ≫ aM = s' ≫ aM`, let `t, t'` be the composites into `Spec(Wm m n)ᵃⁿ`. They
  agree after `p₁`. Their composites after `p₂` land in `O n` and are related through
  `Wm n n` (symmetry and transitivity of the relation), so they are equal by `htriv`; hence
  `t = t'` (`jointly_mono`) and `s = s'`. `mono_bM` is symmetric.
- `exists_of_aRel`: a joint factorization `t` through `Spec(Wm m n)ᵃⁿ` has image in
  `SSet m n`, so it factors through `DS m n` (`domainLift`).
- `chartRelation`: `aM`, `bM` are étale monomorphisms, hence open immersions
  (`openImmersion_of_etale_of_mono`). Reflexivity, symmetry and transitivity of the relation
  on maps from test spaces follow from `exists_of_aRel` and `aRel_of_lift` together with
  `aRel_refl`, `ARel.symm` and `ARel.trans` (module `SpaceChartRelation`).

## Provenance

Derived. This is the gluing step of Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), Lemma 4.2.3 and its proof, pp.20–21
(`conrad-temkin-2009-nonarchimedean-analytification`), applied to an open cover on which the
equivalence relation is trivial, so that each local quotient is the open set itself: the
overlap `Rᵢⱼ = p₁⁻¹(Uᵢ) ∩ p₂⁻¹(Uⱼ)` maps isomorphically onto open subsets of `Uᵢ` and `Uⱼ`.
The pieces are open subsets of analytifications of elementary étale charts (Stacks Project,
Decent Algebraic Spaces, Lemma 68.11.4, Tag 0BBP, and Definition 68.11.5, Tag 0BGU,
`stacks-decent-spaces-chapter-ed88ff78-2026-11-05`) instead of the Galois-split charts of
Conrad–Temkin, Lemma 4.3.3.
