# Points of the Chevalley group normalizing the torus

Module `Langlands.GroupScheme.SplitExistence.Normalizing`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). The Weyl representative
`n_i = x_i(1) x_{-i}(-1) x_i(1)` is classical (Steinberg, *Lectures on Chevalley Groups*, §3).
Its scheme-theoretic normalizing property, in the form of the Library's `IsNormalizingPoint`, is
derived content.

## Declarations

- `φ_sl2Weyl_eq` (any commutative ring `R`):
  `φ_i([[0, 1], [-1, 0]]) = x_i(1) x_{-i}(-1) x_i(1)`. It follows from the `SL₂` factorization
  `sl2Weyl_eq` and the fields `φ_upper`, `φ_lower`.
- `φ_sl2Weyl_mul_torusHom` (any `R`):
  `φ_i(w) · diag(χ(wt c)) = diag(χ(s_i(wt c))) · φ_i(w)`. Compare entries: a nonzero entry
  `(c, d)` of `φ_i(w)` has `wt c = s_i(wt d)` (`weyl_weight`).
- `gaBase s`: the base point of `𝔾ₐ` over `Spec k` with coordinate `s`. `gaCoord_gaBase`
  recovers the coordinate.
- `ChevGroup.weylPoint i`: the `k`-point `u_i(1) · u_{-i}(-1) · u_i(1)` of the Chevalley group,
  where `-i` is `reflectionPerm i i`.
- `ChevGroup.pointsEquiv_weylPoint`: its image in `GL_n(Γ(Spec k))` is `φ_i(w)`.
- `ChevGroup.pointsEquiv_constantPoint_weylPoint`: the same holds for the constant family of
  `n_i` over every test scheme `T`. This is the previous lemma restricted along `T → Spec k`
  (`pointsEquiv_naturality`, `x_map`).
- `ChevGroup.comp_t_innerIso_comp_i`: in `GL_n`, a torus point `x` conjugated by `n_i` is the
  conjugate of `x ≫ torusToGL` by the matrix of `n_i`. This uses the Library's
  `innerIso_hom_comp` and `comp_innerIso_hom`.
- `ChevGroup.comp_torusEnd_t_comp_i`: the analogous identity for `torusEnd w` followed by `t`.
- `ChevGroup.isNormalizingPoint_weylPoint`: **`IsNormalizingPoint G.t (weylPoint i)
  (torusAut s_i)`**, where `s_i` is the reflection `P.reflection i` as an additive automorphism
  of `X` (module `TorusAut`). Both sides are compared on points over every test scheme, after
  composing with the monomorphism `i : G ⟶ GL_n`. The left side is
  `φ_i(w) diag(χ(wt c)) φ_i(w)⁻¹`, and the right side is `diag(χ(s_i(wt c)))`. These agree by
  `φ_sl2Weyl_mul_torusHom`.
