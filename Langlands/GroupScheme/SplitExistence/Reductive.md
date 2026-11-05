# The Chevalley group is reductive

Module `Langlands.GroupScheme.SplitExistence.Reductive`, namespace
`Langlands.GroupScheme.SplitExistence` (the main part is in `ChevalleyData.ChevGroup`). Internal
helper of the proof of the split reductive Existence Theorem (task 2132924b). It proves the
geometric condition in the Library's `IsConnectedReductive`: the base change of the Chevalley
group to an algebraic closure `k̄` of `k` has trivial unipotent radical. This is derived
content. The group theory is in module `UnipotentNormal`.

## Declarations

- `postComp f T`: postcomposition with a group-scheme homomorphism `f`, as a monoid hom on
  points over `T`.
- `ChevGroup.geomGroup`: the base change `G_{k̄}` of `G.H` along `Spec k̄ → Spec k`.
  `ChevGroup.geomPoint` is the test object `Spec k̄` over itself, whose maps to a scheme are its
  rational points.
- `ChevGroup.geomMat`: rational points of `G_{k̄}`, as matrices in `GL_n(k̄)`. Identify them
  with `k̄`-valued points of `G` over `k` (Library `baseChangeBasePointsEquiv`), compose with
  `i : G ⟶ GL_n`, and read off the matrix (`glExt`). `geomMat_apply` unfolds the definition.
- `geomMat_mem`: these matrices lie in `Γ(k̄)` (the field `points` of a stage, module
  `Generation`).
- `geomMat_injective`: `geomMat` is injective, because `i` is a monomorphism.
- `chevSub_le_range_geomMat`: every element of `Γ(k̄)` is the matrix of a rational point. The
  generators `diag(χ(wt c))` and `x_j(s)` are the matrices of `k̄`-points of `D(X)` and `𝔾ₐ`,
  pushed into `G` by `t` and `u j`.
- `ChevGroup.geomRep`: the base change of `i`, followed by the Library isomorphism
  `(GL_{n,k})_{k̄} ≅ GL_{n,k̄}` (`GeneralLinear.baseChangeIso`). It is a matrix representation of
  `G_{k̄}`.
- `baseChangeBasePointsEquiv_eq`: the Library comparison of base points is precomposition
  with the identity of `Spec k̄`.
- `geomMat_eq_pointMatrix`: `geomMat g` is the matrix `geomRep.pointMatrix g`, read in `k̄`.
  This uses `pointsEquiv_comp_baseChangeIso_hom` and `baseChangePointsEquiv_comp`.
- `geomPointIso`: the `k̄`-valued points over `k̄` (`extPoint`) are the rational points.
- `ChevGroup.hasTrivialUnipotentRadical` (`J` finite, `P` reduced):
  **`HasTrivialUnipotentRadical G_{k̄}`**. Let `i : R ⟶ G_{k̄}` be a smooth, connected,
  unipotent closed subgroup with normal range. The matrices `geomMat (h ≫ i)` of rational
  points `h` of `R` form a subgroup `N` of `Γ(k̄)`.
  - `N` is normalized by `Γ(k̄)`. Every element of `Γ(k̄)` is the matrix of a rational point
    `g` (`chevSub_le_range_geomMat`), and `g` normalizes the range of `i`.
  - The elements of `N` satisfy `(M - 1)ⁿ = 0`. Since `R` is unipotent, this holds for its
    representation `geomRep.restrict i` (Library
    `pointMatrix_sub_one_pow_eq_zero_of_isUnipotent`), and `geomMat_eq_pointMatrix` transfers
    it.
  - Hence `N = 1` (`eq_bot_of_unipotent`, `k̄` is infinite), so `h ≫ i = 1` for every rational
    point `h` (`geomMat_injective`).
  - `R` is reduced (smooth over a field) and locally of finite type, and `G_{k̄}` is separated
    (affine). So `i` equals the trivial morphism (`ext_of_extPoints`, module `ExtPoints`, with
    `geomPointIso`), and its range is trivial.
