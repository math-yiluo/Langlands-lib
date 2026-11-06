# Exponents through the graded pieces of the geometric lemma

Fix a field `k` with a topology, a group scheme `G` over `k` with the canonical
topology on `G(k)`, and represented parabolics `P = M N` and `Q = L U` of `G`.
The represented geometric lemma
(`Langlands/Representation/Geometric/RepresentedGeometricLemmaStatement.lean`)
writes `r_Q ∘ i_P` as glued from pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}`, one for each
`GeometricLemmaIntersectionDatum` `D`. Here `P' = M' N'` is a parabolic of `M`,
`Q' = L' U'` is a parabolic of `L`, and `ι` is restriction along the
topological-group isomorphism `e : L'(k) ≃ M'(k)` of `φ : L' ≅ M'`.

This internal supporting module proves that a generalized eigencharacter of a glued
functor occurs in one of its pieces. It also proves that an exponent of a split
component `A_L` on a piece comes, by restriction, from a normalized Jacquet
exponent of the Levi `M'` along `P'`.

## Declarations

- `Langlands.GroupScheme.IsSplitComponent.comp_iso`: if `i : A → G` is a split
  component and `e : G ≅ G'`, then `i ≫ e.hom` is a split component of `G'`.
- `Langlands.IsGluedFrom.exists_isGeneralizedEigencharacter`: let `F` be glued
  from `pieces : Fin n → C ⥤ Rep R G` (`IsGluedFrom`), and let `j : H →* G` and
  `χ : H →* Rˣ`. If `χ` is a generalized eigencharacter of `(F.obj X).ρ.comp j`,
  then for some `i` it is a generalized eigencharacter of
  `((pieces i).obj X).ρ.comp j`.

The following are in the namespace
`Langlands.Aubert.General.RepresentedParabolic`, where `p, l, r` is a represented
parabolic `P = M N` of `G` with its hypotheses.

- `leviPointsEquiv_comp_map`: for every `a : A → M`, `leviPointsEquiv` (from
  `M(k)` onto its image in `G(k)`) composed with the map of `a` on points equals
  `splitComponentPointsMap (l ≫ p) a`.
- `isNormalizedJacquetExponent_iff_leviJacquet`: for a split component
  `a : A → M`, a smooth representation `π` of `G(k)` and `χ : A(k) →* ℂˣ`,
  `IsNormalizedJacquetExponent p l r … ha π χ` holds exactly when `χ` is a
  generalized eigencharacter of `leviJacquetFunctor.obj π`, a representation of
  `M(k)`, restricted along the points of `a`.
- `exists_isGeneralizedEigencharacter_of_leviInduction` (Renard VII.1.1 (i)
  stated for representations of `M(k)`): let `a : A → M` and `aG : AG → G` be
  split components, and let `f : AG → A` satisfy `f ≫ a ≫ l ≫ p = aG`. Let `τ`
  be an admissible smooth representation of `M(k)`, and let `χ` be a generalized
  eigencharacter of `leviInductionFunctor.obj τ` restricted along the points of
  `aG`. Then there is `ψ : A(k) →* ℂˣ` such that
  - `ψ` has open kernel for the split-component topology,
  - `ψ` is a generalized eigencharacter of `τ` restricted along the points of
    `a`, and
  - `ψ ∘ f = χ` on points.
- `GeometricLemmaIntersectionDatum.exists_isNormalizedJacquetExponent_of_piece`:
  let `D` be an intersection datum for `z`, let `a : A → L` and
  `a' : A' → L'` be split components, and let `f : A → A'` satisfy
  `f ≫ a' ≫ (L' → Q') ≫ (Q' → L) = a`. Let `σ` be a smooth representation of
  `M(k)` whose Jacquet module along `P'`
  (`leviJacquetFunctor D.p' D.l' D.r' …`) is admissible, and let `χ` be a
  generalized eigencharacter of `D.pieceFunctor.obj σ` restricted along the
  points of `a`. Then there is `ψ : A'(k) →* ℂˣ` such that
  - `ψ` is a normalized Jacquet exponent of `σ` along `P'` for the split
    component `a' ≫ φ.hom` of `M'`, and
  - `ψ ∘ f = χ` on points.

## Proofs

- `IsSplitComponent.comp_iso`: split subtori are preserved by `e`
  (`IsSplitSubtorus.comp_iso_iff`), and so is centrality (`IsCentral.comp_iso`).
  For maximality, a central split torus `i'` of `G'` through which `i ≫ e.hom`
  factors gives the central split torus `i' ≫ e.inv` of `G`, through which `i`
  factors. The maximality of `i` then makes the factor an isomorphism.
- `IsGluedFrom.exists_isGeneralizedEigencharacter`: unfold `IsGluedFrom` into a
  permutation `e` and an ordered filtration `s` whose graded pieces are
  isomorphic to `pieces (e i)`. The published
  `RepFunctorFiltration.exists_graded_isGeneralizedEigencharacter` gives a graded
  piece of `s` carrying `χ`. The isomorphism `iso.app X` of that graded piece
  with `pieces (e i)` is an equivalence of representations, and composing it with
  `j` (`Cohomology.HyperextAbutment.equivComp`) gives an equivalence of the
  restricted representations. `isGeneralizedEigencharacter_iff_of_equiv` then
  transfers `χ`.
- `leviPointsEquiv_comp_map`: both sides send a point to the same element of
  `G(k)`, so they agree by `Subtype.ext rfl`.
- `isNormalizedJacquetExponent_iff_leviJacquet`: rewrite with the published
  `isNormalizedJacquetExponent_iff` and with `leviPointsEquiv_comp_map`. The two
  sides then agree by definition, because `leviJacquetFunctor` is
  `jacquetFunctor` followed by pullback along `leviPointsEquiv`.
- `exists_isGeneralizedEigencharacter_of_leviInduction`: let `W` be the pullback
  of `τ` to the image of `M(k)` in `G(k)` along `leviPointsEquiv⁻¹`. It is
  admissible by `isAdmissible_comp_continuousMulEquiv`. The induced
  representation `leviInductionFunctor.obj τ` is by definition
  `inductionFunctor.obj W`, so `generalizedWeightSpace_ne_bot_iff` turns the
  hypothesis on `χ` into the nonvanishing of `groupWeightSpace haG … χ`. The
  points of `f` are compatible with `a`, `aG` and `splitComponentPointsMap`
  because `f ≫ a ≫ l ≫ p = aG`. The published Renard VII.1.1 (i),
  `inducedExponent_restrict`, then gives `ψ` with open kernel, a nonzero
  generalized weight space in `W` and `ψ ∘ f = χ`. Finally,
  `generalizedWeightSpace_ne_bot_iff` turns the nonzero weight space into an
  eigencharacter statement, and `W` restricted along
  `splitComponentPointsMap (l ≫ p) a` equals `τ` restricted along the points of
  `a`, because `leviPointsEquiv⁻¹ ∘ leviPointsEquiv` is the identity.
- `exists_isNormalizedJacquetExponent_of_piece`: let `J` be the Jacquet module
  of `σ` along `P'` and `τ` its pullback along `e` to `L'(k)`. `τ` is admissible
  by `isAdmissible_comp_continuousMulEquiv`. The piece at `σ` is by definition
  `leviInductionFunctor D.q' D.lQ' … τ`, so the previous theorem, applied in the
  ambient group `L` to the parabolic `Q'` with `aG := a`, gives `ψ` with
  `ψ ∘ f = χ`, where `ψ` is a generalized eigencharacter of `τ` restricted along
  the points of `a'`. Since `e x = φ(x)` on points (`D.e_apply`), that restricted
  representation equals `J` restricted along the points of `a' ≫ φ.hom`.
  `isNormalizedJacquetExponent_iff_leviJacquet` then identifies this with the
  normalized Jacquet exponent condition.

## Provenance and scope

This is derived content for the proof of Renard VII.2.2
(`LeviInductionNormalizedTemperedStatement`), PDF pp.233–234. Renard applies the
geometric lemma VI.5.1 to `r_Q i_P σ` and observes that an exponent of `A_L` on
`r_Q i_P σ` is an exponent on one of the pieces `i^L_{L∩w⁻¹Pw} ∘ w ∘ r^M_{wQ∩M}`.
By VII.1.1 it is then the restriction of an exponent of `A_{L∩w⁻¹Mw}` on
`w ∘ r^M_{wQ∩M}(σ)`. This module carries out this step for the represented pieces
of `pieceFunctor`. Renard's twist by `w` appears here as the pullback along `e` and
the split component `a' ≫ φ.hom` of `M'`.

The admissibility of the Jacquet module of `σ` along `P'` is a hypothesis of
`exists_isNormalizedJacquetExponent_of_piece`, because the published
VII.1.1 (i) requires an admissible inducing representation. The module does not
prove that hypothesis, and it does not use the conjugation compatibility
`φ_comp` or the torus fields of the datum.
