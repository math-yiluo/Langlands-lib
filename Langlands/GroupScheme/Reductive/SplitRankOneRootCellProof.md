# Proof: root groups and the open cell in semisimple rank one

Author: Worker 239.

Module `Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof`. It proves

`splitRankOneRootCell : SplitRankOneRootCellStatement.{u}`

with no hypotheses. It assembles the cell data of `RankOneCellData`, the Weyl-point
argument of `RankOneRootCellWeyl` and the descent to algebraically closed fields of
`SplitRankOneRootCellUniversal` (Worker 1388). The published inputs are the Library
theorems `dynamicCentralizerReductive`, `rankOnePositiveRootUniqueness` and
`splitRootLieLine`, which discharge the hypotheses `hDCR`, `hPRU` and `hLL` of
`rankOne_exists_rootCell`.

## Definitions (namespace `Langlands.GroupScheme.RankOneRootCellRelation`)

`crd` is `RootCell.crd`, the coordinate of a point of `𝔾ₐ`. `pb Z x` is
`WeylData.pb`, the pullback to `Z` of a global section `x` of `Spec k`.

- `scaleEquiv c Z`, for a unit `c` of `Γ(Spec k, ⊤)`, is the multiplicative equivalence of
  the points of `𝔾ₐ` over `Z` that multiplies the coordinate by `pb Z c`; its inverse
  multiplies by `pb Z c⁻¹`.
- `scaleIso c : Ga k ≅ Ga k` is the group automorphism `isoOfPoints (scaleEquiv c) _`,
  multiplication by `c`.
- For `D : WeylData k`: `D.unitβ` is the constant `β = D.cβ` (from `xp(1) n = xm(β) γ xp(δ)`
  over `Spec k`) as a unit, by `cβ_isUnit`. `D.xm' = (scaleIso D.unitβ).hom ≫ D.xm` is the
  rescaled negative root group, `xm'(Y) = xm(β Y)`.

## Results

- `crd_gpt`, `gpt_crd`, `crd_mul` and `crd_weightPointAction` translate between `gpt` of
  `RankOneRootCellRelation` and `crd`: the coordinate of `gpt x` is `x`, `crd` is additive,
  and the weight action of `χ` multiplies the coordinate by `χ(t)`. `pb_mul`, `pb_one` and
  `appTop_pb`: `pb Z` is a ring map, natural in `Z`.
- `scaleEquiv_naturality`, and `comp_scaleIso_hom`: `a ≫ scaleIso c = gpt (pb Z c · crd a)`.
  An instance makes the underlying morphism of schemes of `scaleIso c` an isomorphism.
- `exists_sq_eq_of_isNormalizingPoint`: suppose `i` represents the dynamic centralizer of
  the cocharacter `h`, `⟨α, h⟩ = 2`, and the `k`-point `n` normalizes `T` through the
  reflection `latticeReflectionIso α h`. Then `n * n = z ≫ i` for a `k`-point `z` of `T`.
- For `D : WeylData k`:
  - `comp_xp` and `comp_xm'`: `a ≫ xp = D.A (crd a)` and `b ≫ xm' = D.B (pb Z β · crd b)`.
  - `conj_xm'`: `T` acts on `xm'` through `-α` by conjugation (clause 2).
  - `tripleCell_xm'`: the cell map of `xm'`, `i`, `xp` is the cell map of `D` precomposed
    with `scaleIso β` on the first factor. `isOpenImmersion_xm'`: it is an open immersion
    (clause 3).
  - `relationOver_xm'`: `RootCell.RelationOver i h xp xm' (Over.mk f)` for every
    algebraically closed field `K` and every `f : Spec K ⟶ Spec k`.
  - `not_inCell_xm'`: over such `Spec K`, if `1 + crd a · crd b = 0`, then
    `RootCell.InCell i xp xm' a b` fails.
  - `isRootCell`: if `G.X.hom` is separated, then `RootCell.IsRootCell i α h xp xm'`, that
    is, `xp` and `xm'` satisfy all five clauses.
- `splitRankOneRootCell : SplitRankOneRootCellStatement.{u}` (namespace
  `Langlands.GroupScheme`).

## The implemented proof

1. **Rescaling.** `scaleEquiv c` is multiplicative by `crd_mul` and `gpt_add`, and natural
   by `comp_gpt`, `appTop_pb` and `RootCell.crd_comp`, so `isoOfPoints` gives
   `scaleIso c`. Its scheme morphism is an isomorphism with inverse that of
   `(scaleIso c).inv`.
2. **`n²` lies in `T`.** By `IsNormalizingPoint.mul`, conjugation by `n * n` acts on `T`
   through the composite of the reflection with itself. The reflection `1 - α ≫ h` is its
   own inverse (its `hom` and `inv` are both `𝟙 T - α ≫ h`), so the composite is the
   identity and `i ≫ innerIso (n * n) = i`. By `comp_innerIso_hom`, `n * n` then
   commutes with the point `s ≫ h ≫ i` of `G` over `Spec k × 𝔾ₘ`, where `s` is the second
   projection, the universal unit. With `Dynamic.mem_centralizer`, `Dynamic.orbit` and
   `comp_eq_constantPoint` this says that `n * n` lies in the dynamic centralizer of `h`. Since `i` represents it (`hC`), `n * n` comes from a point `z` of `T`
   (`hC.pointsEquiv`).
3. **Clauses 1 to 3.** Clause 1 is `D.hxp`. For clause 2, `comp_xm'` reduces the
   conjugation to `I_mul_B` for `xm` (`t xm(y) = xm(α(t)⁻¹ y) t`), and the scalars agree by
   `crd_weightPointAction`, `cu_neg` and `ring`. For clause 3, the cell map of `xm'` is
   `(scaleIso β ▷ _) ≫ D.cellMul` by `MonObj.comp_mul` and the whiskering identities; its
   `left` is the composite of an isomorphism (the image of `scaleIso β ▷ _` under
   `Over.forget`) with the open immersion `D.open_cell`.
4. **Clauses 4 and 5 over algebraically closed fields.** Over `Spec K` with `K`
   algebraically closed, the global sections satisfy `SqField` (`sqField_Γ_Spec`). With
   `comp_xp` and `comp_xm'`, `xp(a) xm'(b) = xp(X) xm(β Y)` for `X = crd a`, `Y = crd b`.
   `rel_of_sqField` writes this as `xm(β u⁻¹ Y) h(u) xp(u⁻¹ X)`, which is clause 5 for
   `xm'` after `comp_xm'` and `comp_xp` on the right side (`relationOver_xm'`). If
   `1 + XY = 0`, a factorization `c` of `xp(a) xm'(b)` through the cell map of `xm'` gives
   the factorization `c ≫ (scaleIso β ▷ _)` through `D.cellMul` (`tripleCell_xm'`), which
   contradicts `not_inCell_of_sqField` (`not_inCell_xm'`).
5. **All test schemes.** `RootCell.inCell_iff_and_relationOver` of
   `SplitRankOneRootCellUniversal`, applied to `relationOver_xm'` and `not_inCell_xm'`,
   gives clauses 4 and 5 over every test scheme; `G.X.hom` is assumed separated
   (`isRootCell`).
6. **`splitRankOneRootCell`.** Take `k`, `G`, `T`, `i`, `P`, the rank-one hypothesis and an
   index `r`. `rankOne_exists_rootCell`, with `dynamicCentralizerReductive`,
   `rankOnePositiveRootUniqueness` and `splitRootLieLine`, gives `xp`, `xm` with the
   conjugation clauses, the open cell, and the fact `hC` that `i` represents the dynamic
   centralizer of `h = P.coroot r`. The pairing `⟨P.root r, P.coroot r⟩ = 2` is
   `RootPairing.root_coroot_two` together with `P.toLinearMap = latticePairing T` (the
   first part of `IsRootDatumOf`). `IsRootDatumOf.exists_normalizing_latticeReflectionIso`
   gives the `k`-point `n` normalizing `T` through the reflection, and step 2 gives
   `n² ∈ T`. `G.X.left` is irreducible by `DynamicConnected.irreducibleSpace_of_smooth`,
   since `G` is smooth and connected. These data form a `WeylData k`. `G` is affine over
   `k`, so `G.X.hom` is separated, and `isRootCell` gives the five clauses for `xp` and
   `xm'`.

## Provenance

The statement formalizes Conrad, *Reductive group schemes*, Theorem 4.1.4, Remark 4.2.4 and
Theorem 4.2.6 over a field (literature `conrad-2014-reductive-group-schemes`); see
`SplitRankOneRootCellStatement`. The root groups `xp` and `xm` come from the dynamic
unipotent subgroups of `±α^∨` (`RankOneCellData`); they are parametrizations of the root
groups in the sense of Conrad's Remark 4.2.4. Rescaling `xm` by the unit `β` replaces it by
the parametrization linked to `xp`, in the sense of the discussion after Theorem 4.2.6
(following SGA 3, Exp. XX, 2.6.1). Relation (4.2.1) is stated in this normalization. The route to clauses 4 and 5 through the
Weyl point (`RankOneRootCellWeyl`) is not Conrad's, who works in `PGL₂`; see that module.
