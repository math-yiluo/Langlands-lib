# The morphism to projective space defined by base-point-free sections

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.LinearSystemMorphismStatement`. It is internal: it is not a
Library statement. It formalizes the morphism to projective space defined by base-point-free
sections, which Milne uses in the proof of Theorem 7.1 (pp.10–11 of
`milne-abelian-varieties-1986-author-2022`, recalling Hartshorne; Hartshorne is not registered
and is cited only through Milne). Compare Stacks Project, Constructions of Schemes, Section 27.14 "Invertible sheaves and morphisms into Proj", Lemma 27.14.1, tag 01NJ, in the registered source `stacks-very-ampleness-support-2026-10-29`, applied to the graded ring map `K[X_0, …, X_n] → Γ_*(X, L)` sending `X_i` to `s i`. The formulation through `T`-points
and pulled-back ratios is our own. Everything is in the namespace
`Langlands.AlgebraicGeometry.LinearSystem`.

Throughout, `K` is a field, `p : X ⟶ Spec K`, `L` is a line bundle on `X` and
`s : Fin (n + 1) → GlobalSections L.obj`. `U_j` denotes `trivializationOpen L.obj (s j)`.
`ProjectiveSpace K n` is `Proj` of `K[X_0, …, X_n]` with its standard grading.

## Scalars and linear combinations

- `eval₂_mul_of_isHomogeneous`: scaling all variables by `c` multiplies the value of a
  homogeneous polynomial of degree `m` by `c ^ m`.
- `scalarsFromBase_comp`: the scalars `K → Γ(T, ⊤)` of `g ≫ q` are the scalars of `q` followed
  by `g^#`. Here `Scheme.Modules.scalarsFromBase q` is Library's map
  `R → Γ(Spec R, ⊤) → Γ(T, ⊤)` for `q : T ⟶ Spec R`.
- `toSpecΓ_SpecMap_scalarsFromBase`: a morphism `q : T ⟶ Spec R` equals
  `T.toSpecΓ ≫ Spec.map (scalarsFromBase q)`.
- `exists_scalarsFromBase_eq`: for a rational point `x` (`x ≫ p = 𝟙`), every global function
  on `Spec K` is the image of a scalar `α ∈ K`.
- `linComb p s c := ∑ i, scalarsFromBase p (c i) • s i`, the section `σ c` of the statement.
- `sectionRatio_linComb`: the ratio of `linComb p s c` to `s₀` along `g` is
  `∑ i, c i * ratio(s i, s₀)`, with `c i` read in `Γ(T, ⊤)` through `scalarsFromBase (g ≫ p)`.
- `basisDiff i j α := e_i - α e_j`, so `linComb p s (basisDiff i j α) = s i - α • s j`;
  `sum_scalarsFromBase_single` and `sectionRatio_linComb_basisDiff` compute its ratio.
- `vanishesAlong_linComb_basisDiff_iff`: for `g` landing in `U_j`, the section
  `s i - α • s j` vanishes along `g` if and only if `ratio(s i, s j) = α` along `g`.

## Point maps

For `g : T ⟶ X` and an index `j`:

- `chartRingHom p s g j : K[X_0, …, X_n] →+* Γ(T, ⊤)` is evaluation at the ratios:
  constants go through `scalarsFromBase (g ≫ p)` and `X_i ↦ ratio(s i, s j)` along `g`
  (`chartRingHom_X`, `chartRingHom_C`). If `g` lands in `U_j`, then `X_j ↦ 1`, a unit
  (`isUnit_chartRingHom_X`). `sectionRatio_linComb_eq_chartRingHom` expresses the ratio of
  `σ c` as the value of the linear form `∑ c_i X_i`.
- `pointMap p s g j hg : T ⟶ ProjectiveSpace K n` is the chart map (module `ChartMap`) of
  `chartRingHom p s g j` through the chart `D₊(X_j)`. It sends `X_i / X_j` to
  `ratio(s i, s j)`.
- `pointMap_eq`: if `g` lands in both `U_j` and `U_k`, the point maps through `D₊(X_j)` and
  `D₊(X_k)` agree. The ring map for `k` is the ring map for `j` rescaled by the unit
  `ratio(s j, s k)` according to degree (`chartRingHom_scale`, from `sectionRatio_mul` and
  `eval₂_mul_of_isHomogeneous`). The result then follows from `chartMap_eq` and
  `chartMap_eq_of_scale`.
- `comp_chartRingHom`, `comp_pointMap`: naturality, `h ≫ pointMap g = pointMap (h ≫ g)`.
- `pointMap_toSpec`: `pointMap g ≫ projectiveSpaceToSpec K n = g ≫ p`.
- `pointMap_preimage`: the preimage of the coordinate chart `D₊(X_i)` is the basic open of
  `ratio(s i, s j)` in `T`.
- `chartRingHom_eq_of_pointMap_eq`: equal point maps through the same chart come from equal
  ring maps. Indeed, `awayLift_eq_of_chartMap_eq` recovers the map on `K[X]_(X_j)`, and
  `eq_of_awayLift_eq` recovers the values on constants (degree 0) and on the variables
  (degree 1), since both ring maps send `X_j` to `1`.

## The glued morphism and its dictionary

Assume `hs : ∀ x, ∃ i, x ∈ nonvanishingLocus L.obj (s i)`.

- `exists_mem_trivializationOpen`, `isOpenCover_trivializationOpen`: the `U_j` cover `X`, by
  Library's `lineBundleResidueOpenComparison` (nonvanishing locus = trivialization open).
- `linearSystemMap p hs : X ⟶ ProjectiveSpace K n` glues (Mathlib's `Cover.glueMorphisms`) the
  point maps of the open immersions `U_j ⟶ X`. They agree on the overlaps `U_j ×_X U_k`
  by naturality and `pointMap_eq`. `ι_linearSystemMap` says that the restriction to `U_j` is
  that point map.
- `comp_linearSystemMap`: for every `g : T ⟶ X` landing in `U_j`,
  `g ≫ linearSystemMap p hs = pointMap p s g j hg`. Two morphisms agree if they agree on an
  open neighbourhood of each point (`Scheme.hom_ext_of_forall`); near `t`, use `U_k`
  containing `g t`, naturality and `pointMap_eq`.
- `linearSystemMap_toSpec`: `linearSystemMap p hs ≫ projectiveSpaceToSpec K n = p`.
- `chartRingHom_eq_of_comp_eq`, `vanishesAlong_linComb_iff_of_comp_eq`: if `g₁, g₂` land in
  `U_j` and have the same image, then their ring maps agree. Hence a linear combination
  `σ c` vanishes along `g₁` exactly when it vanishes along `g₂`.
- `comp_eq_of_sectionRatio_eq`: if `g₁, g₂` land in `U_j`, satisfy `g₁ ≫ p = g₂ ≫ p`, and
  have equal ratios `ratio(s i, s j)` for all `i`, then they have the same image.
- `mem_trivializationOpen_of_comp_mem`: for a field `K'` and `y : Spec K' ⟶ X` whose image
  point lies in `D₊(X_i)`, the point of `X` lies in `U_i`. Otherwise `s i` vanishes along `y`
  (`vanishesAlong_iff_not_mem`), so its ratio is zero and the preimage of `D₊(X_i)` is empty.
- `comp_mem_coordinateOpen`: a `T`-point landing in `U_j` maps into `D₊(X_j)`.
