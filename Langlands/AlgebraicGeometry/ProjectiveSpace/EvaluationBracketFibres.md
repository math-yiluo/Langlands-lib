# Finitely many evaluation configurations in the fibres of the bracket map

The setting is that of `EvaluationBracketAtlas`: a scheme `X`, a module sheaf
`E`, labels `Λ`, and morphisms `ev r : E ⟶ Q r`. Let `K` be a field in the
universe of `X`.

## Field models

`FieldModel ev M t` covers a `K`-point `t : Spec K ⟶ X`. It records the
following data.

- `E'`, `Q' r` and `ev' r`: evaluation data over `Spec K`.
- Isomorphisms `α : t^* E ≅ E'` and `β r : t^* (Q r) ≅ Q' r` such that
  `α.hom ≫ ev' r = t^*(ev r) ≫ (β r).hom`.
- Quasi-coherence of `E'` and of every `Q' r`.
- `finrank K Γ(E') = M` and `finrank K Γ(Q' r) = 1`.

Two field models `F`, `F'` are `Equivalent` if some isomorphism
`φ : F.E' ≅ F'.E'` satisfies `φ.hom ≫ F'.ev' r = F.ev' r ≫ ψ.hom` for every
label `r`, for some isomorphism `ψ : F.Q' r ≅ F'.Q' r`.

## A chart at a field point

Let `t` land in the open of a chart `C`.

- `ε k` is the image in `Γ(E')` of the pulled-back frame vector `C.eV k`, and
  `κ r` is the image in `Γ(Q' r)` of the pulled-back generator `C.q r`.
- `ev'_ε` states that `ev' r` sends `ε k` to the pulled-back coefficient times
  `κ r`. The proof uses the compatibility of `α` and `β`, naturality of section
  pullback and its semilinearity (`sectionPullbackLE_smul`).
- `κ_ne_zero` holds because pullbacks of local generators are local generators
  (FLT `IsFrameOn.pullbackLocalSection`) and `Γ(Spec K, ⊤)` is
  nontrivial.
- `ofΓ` views global sections as a `K`-vector space. `smul_eq_ψK` compares
  multiplication by functions with the `K`-scalar action through
  `Scheme.ΓSpecIso`. `ℓ r` is `ev' r` on global sections as a `K`-linear map, and
  `fieldCoef` are the coefficients in `K`.
- `linearIndependent_ε` holds because the coefficients at the frame labels are
  `1` on the diagonal and `0` elsewhere and the `κ` are nonzero. Since
  `finrank K Γ(E') = M`, `εB` is a basis.

Fix `n > 0`, trivializations `τ` and an algebraically closed `K`.

- `gaugeVal r` is the value of the gauge of `C.q r` at `t`. It is nonzero, and
  `root r` is a chosen `n`-th root of it.
- `normA r k = fieldCoef r k * root r` is the normalized evaluation matrix, and
  `normκ r = (root r)⁻¹ • κ r`. `ℓ_εB` states that `ℓ r (εB k)` is
  `normA r k • normκ r`.
- `poweredMinor_normA` states that the `n`-th power of the maximal minor of
  `normA` at a tuple `σ` is the value at `t` of `C.coord τ σ`.

## Equivalence from matrices

- `specIso` lifts a `K`-linear equivalence of global sections of quasi-coherent
  modules on `Spec K` to an isomorphism of modules. It is built from
  `SpecQuasicoherentHoms.isoOfIso`.
- `lineEquiv` is a linear equivalence of one-dimensional spaces sending a given
  nonzero vector to another; `lineEquiv_apply` records this.
- `FieldModel.equivalent_of_vecMul` covers two field models with source bases
  `b`, `b'` and nonzero target vectors `κ`, `κ'`. The evaluation matrices
  `A`, `A'` satisfy `ℓ r (b k) = A r k • κ r`, and similarly for the primed
  data. If `A r ᵥ* G = A' r` for every row and one invertible matrix `G`, then
  the field models are equivalent. The source isomorphism is the matrix `G⁻¹` in
  the two bases. The target isomorphisms send `κ r` to `κ' r`. Equality of
  morphisms is checked on global sections with `SpecQuasicoherentHoms.hom_ext`.

## Main theorem

`exists_finset_equivalent` assumes the following.

- Finitely many labels and `M > 0`.
- A morphism `p : X ⟶ Spec R`.
- Covering charts, `n > 0` and trivializations `τ`.
- An enumeration of the label tuples.
- An algebraically closed field `K`, and a field model for every `K`-point.

Let `j` be the glued morphism `CoordinateAtlas.atlasMap p (isAtlas …)`. For
every `K`-point `y` of `ProjectiveSpace R m` there is a finite set `s` of
`K`-points of `X` such that every `t` with `t ≫ j = y` has a field model
equivalent to that of some member of `s`. The set is empty if no point lies over
`y`.

Proof: fix one point `t₀` over `y` and a coordinate that is a unit at `t₀`
(`exists_isUnit_pull`). For every `t` over `y`, `exists_unit_of_comp_eq` gives a
unit relating the pulled-back coordinates at `t` and at `t₀`. By
`poweredMinor_normA` the powered minors of the normalized matrices of all points
over `y` are thus nonzero multiples of one fixed function, nonzero at a fixed
pivot. `PoweredMinors.exists_finset_of_projectively_equal_poweredMinors` gives
finitely many representatives up to one invertible matrix, and
`equivalent_of_vecMul` converts this into equivalence of field models.

## Provenance

This is an internal construction, not taken from a literature source. It
implements step 5 of the intended proof recorded in the Markdown of
`TorsionBracketMapStatement`. Over an
algebraically closed field the target generators are first rescaled so that
their gauges are `1`, which gives `normA`. Target rescaling alone does not make
the entries of `normA` take finitely many values over a fixed projective point:
on `Spec K[z, z⁻¹]` with one label, `M = n = 1` and identity evaluation, `normA`
at the point `z = a` is `[a]`, although all these points have the same image in
`P⁰`. A second normalization of the source basis is needed. For a common
nonvanishing pivot, right multiplication by the inverse of the pivot submatrix
gives a matrix whose entries have `n`-th powers equal to ratios of powered
brackets, and these ratios are fixed by the projective point. Hence there are
only finitely many classes of `normA` under common right multiplication by an
invertible matrix. This second step is
`PoweredMinors.exists_finset_of_projectively_equal_poweredMinors`, and
`equivalent_of_vecMul` turns each such class into one equivalence class of field
models.
