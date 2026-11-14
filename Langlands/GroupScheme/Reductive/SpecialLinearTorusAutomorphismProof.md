# Proof: torus-preserving automorphisms of `SL_{n+1}` are matrix conjugations, possibly with inverse transpose

Module `Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof`,
namespace `Langlands.GroupScheme.SpecialLinearTorusAutomorphism`.

The main theorem `specialLinearTorusAutomorphism` proves
`Langlands.GroupScheme.SpecialLinearTorusAutomorphismStatement.{u}` at every
universe `u`. The statement and its Markdown are imported unchanged. It uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Throughout, `𝐒𝐋 = SpecialLinear.groupScheme (Fin (n+1)) (CommRingCat.of k)` over a
field `k`, and `p` is a split pinning of `𝐒𝐋`. The helper modules are
`Langlands.LinearAlgebra.RootPairingTypeACoord`, which proves `Aut = ±W` for type `A`
coordinates, and `Langlands.GroupScheme.Reductive.SpecialLinearTypeACoord`, which
builds the coordinates of the diagonal torus.

## Auxiliary declarations

- `negIso T`: the inversion automorphism `-𝟙` of a commutative group scheme.
- `comp_innerIso_inv`: on points, the inverse of the inner automorphism by a base
  point `g` is conjugation by the inverse.
- `pointMatrix_refl`: `SpecialLinearInnerForm.pointMatrix (Iso.refl _)` is
  `SpecialLinear.pointsEquiv`.
- **`exists_matrix_of_weyl`** (Weyl case). Assume `w ∈ p.rootDatum.weylGroup` with
  `w.weightEquiv χ = t.hom ≫ χ`. Then `f` is conjugation by one `X ∈ GL_{n+1}(k)` on
  every test scheme `Z`, with `X` mapped through `scalarMap Z`. Proof: since the
  root-datum weight map is the inverse of `characterAut t`,
  `IsRootDatum.abstractWeylImage_le` gives `characterAut t ∈ weylImage p.inclusion`.
  The adjoint quotient comes from `adjointQuotientExistence`.
  `SplitPinning.exists_adjointPoint_of_weylImage` writes `f` as the inner action of a
  `k`-point of the adjoint quotient. The published bridge
  `SpecialLinearInnerForm.exists_matrix_for_adjoint_basePoint`, with the identity
  presentation, gives the matrix.
- `exists_conj_diagonal`: by the published maximal split torus conjugacy theorem
  (`maximalSplitTorusConjugacy`), the pinned torus is carried to the diagonal torus
  by the inner automorphism of some `g : k`-point, through a torus isomorphism `e`.
- `exists_typeACoord`: the pinned root datum `p.rootDatum` has type `A_n`
  coordinates, and its coroots span the cocharacter lattice. Both facts are
  transported along the root-datum equivalence
  `rootDatumEquivOfTorusCompatibleIso` of the previous square. They start from a
  coordinate root datum of the diagonal torus: `exists_coordinateRootDatum`,
  `FinSucc.typeACoord`, and `corootSpan_eq_top`.
- `twistIso g`: `innerIso g ≪≫ contragredientIso ≪≫ (innerIso g).symm`, the
  inverse transpose conjugated into the pinned torus. The published
  `SpecialLinear.contragredientIso` is used.
  - `twistIso_hom_comp_hom`: it is an involution.
  - `inclusion_comp_twistIso_hom`: it acts on the pinned torus by `negIso`. This
    uses `FinSucc.diagonalTorus_comp_contragredientIso_hom`.
- `exists_pointsEquiv_constantPoint`: a `k`-point of `𝐒𝐋` has one matrix
  `C ∈ SL_{n+1}(k)` whose image under `scalarMap Z` is its constant point on each
  `Z`. The proof uses `pointsEquiv_naturality` and `Γ(Spec k) ≅ k`.
- `toGL_map`, `toGL_pointsEquiv_twistIso`: in `GL`, the point formula for
  `twistIso g` is `c⁻¹ κ(c h c⁻¹) c`, where `κ` is `GeneralLinear.matrixContragredient`
  and `c` is the matrix of the constant point.
- `conj_identity`: a group identity for a multiplicative automorphism `κ`:
  `c⁻¹ κ(c (y h y⁻¹) c⁻¹) c = (c⁻¹ κ(c y)) κ(h) (c⁻¹ κ(c y))⁻¹`.
- **`exists_matrix_of_neg_weyl`** (inverse-transpose case). Assume
  `w ∈ weylGroup` with `w.weightEquiv χ = -(t.hom ≫ χ)`. Then on every test,
  `f(h) = X (h⁻¹)ᵀ X⁻¹` for one `X ∈ GL_{n+1}(k)`. Proof: take `g₀`, `e` from
  `exists_conj_diagonal`. Then `f ≪≫ twistIso g₀` is compatible with
  `t ≪≫ negIso`, whose weight action is that of `w`. The Weyl case gives a matrix
  `Y` for `f ≫ ψ`, where `ψ = twistIso g₀`. Since `ψ` is an involution,
  `f(h) = ψ(Y h Y⁻¹)`. The point formula for `ψ`, the naturality
  `GeneralLinear.matrixContragredient_map` and `conj_identity` then give
  `X = c₀⁻¹ κ(c₀ Y)`, where `c₀` is the `GL` image of `C`. Finally
  `matrixContragredient_coe` turns `κ(h)` into `(h⁻¹)ᵀ`.

## The main theorem

Let `δ` and `θ` be as in the statement. By `rootDatumEquivOfTorusCompatibleIso_weightMap`,
`δ.weightEquiv χ = t.hom ≫ χ`. Take type `A` coordinates `C` and the coroot spanning
fact from `exists_typeACoord`.

- **`θ` fixes every simple index.** `Base.span_int_coroot_support` shows that the
  coroots of `p.base.support` span the coroot span, which is everything. So
  `eq_one_of_indexEquiv_eq` gives `θ = 1`. Then
  `basedRootDatumProjection_eq_one_iff` gives `δ ∈ weylGroup`, and
  `exists_matrix_of_weyl` (with `w = δ`) supplies `x`. The second implication has a
  false premise.
- **`θ` moves some simple index.** Then `δ ∉ weylGroup`: otherwise `θ = 1` would
  fix every index. `mem_weylGroup_or_exists_neg` gives `w ∈ weylGroup` with
  `w.weightEquiv = -δ.weightEquiv`, and `exists_matrix_of_neg_weyl` supplies `x`.
  The first implication has a false premise.

In both cases the statement's `g` is turned into a scheme point by
`(pointsEquiv Z).symm`, and `MulEquiv.apply_symm_apply` removes the round trip.

## Relation to the literature

The statement cites Milne, *Algebraic Groups* (2017), 23.44–23.47 and the type `A`
discussion on printed p.524. The Lean proof does not follow that route through
the full `Aut(G) → Aut(Ψ₀)` sequence. It shows directly that, for type `A_n`, the
root-datum automorphism `δ` is `±` a Weyl element. Compare `A(R) = W(R) × {1, -1}`
for `A_l`, `l ≥ 2`, in Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6* (Springer, 2002), registered as `bourbaki-lie-iv-vi-2002-scribd-original-text` (retained HTML, SHA-256 `b9f6932507d4da5351eb45a68387ad76dfa58dd118c0da97f01501293f97546c`), Plate I, item (XI). The `+` case is inner, through
the published pinned Weyl innerness and the adjoint-point matrix bridge. The `−`
case is reduced to the `+` case by composing with a conjugate of the inverse
transpose. No restriction on the characteristic or on `n` is needed. The proof
treats every `n`, including `n = 0, 1`, uniformly by the case split on whether
`θ` fixes the simple indices. It never needs to decide which case occurs for a
particular `n`.
