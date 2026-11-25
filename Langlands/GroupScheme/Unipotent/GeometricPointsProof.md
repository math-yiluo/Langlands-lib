# Unipotence of smooth groups through geometric points: proof

`Langlands.GroupScheme.smoothUnipotentGeometricPoints` proves
`Langlands.GroupScheme.SmoothUnipotentGeometricPointsStatement.{u}` for every
universe `u`. The theorem's type is exactly that proposition, with no extra
hypotheses. The proposition encodes Milne (2017), Corollary 14.12. See the
[statement and source comparison](GeometricPointsStatement.md).

Throughout, `k : Type u` is a field and `G` is a group scheme over `Spec k`
with `Smooth G.X.hom` and `IsAffineHom G.X.hom`. Write `K` for
`AlgebraicClosure k`, `b` for `Spec.map (CommRingCat.ofHom (algebraMap k K))`
and `G_K` for `(GroupScheme.baseChange b).obj G`.

## Route

The proof reduces the statement to two published results, as in Milne's
proof of 14.12, which combines 14.9 and 14.10.

- Milne 14.10 over a perfect field:
  `Langlands.GroupScheme.perfectFieldUnipotentRationalPoints`
  (`Langlands.GroupScheme.Unipotent.RationalPointsProof`), the published
  proof of `PerfectFieldUnipotentRationalPointsStatement`. For an affine group
  scheme `H`, locally of finite type over a perfect field, its first part says
  that if `H` is unipotent then every rational point acts by a unipotent
  matrix in every matrix representation of `H`. Its second part says the
  converse when the rational points are schematically dense, that is, when
  every closed immersion into `H.X.left` through which every rational point
  factors is an isomorphism. It is applied to `H = G_K` over `K`. Mathlib's
  instance `IsAlgClosed.perfectField` makes `K` perfect.
- Milne 14.9 in both directions:
  `Langlands.GroupScheme.unipotentFieldExtensionStatement`
  (`Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof`) says that
  `G_K` is unipotent if `G` is, for `G` with affine structure map and locally
  of finite type. `Langlands.GroupScheme.unipotentFieldReflection`
  (`Langlands.GroupScheme.Unipotent.FieldReflectionProof`) says that `G` is
  unipotent if `G_K` is, for `G` with affine structure map.

The only new mathematics is that the rational points of `G_K` are
schematically dense. This is where smoothness is used.

## Instances on the base change

The structure morphism of `G_K` is by definition
`Limits.pullback.snd G.X.hom b`. Mathlib's base-change instances give
`IsAffineHom`, `LocallyOfFiniteType` and `Smooth` for it. The published
lemma `Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`
then shows that `G_K.X.left` is reduced. Over `k`, `LocallyOfFiniteType G.X.hom`
is found by instance search from `Smooth G.X.hom`.

## Schematic density of rational points

`Langlands.GroupScheme.isIso_of_forall_rationalPoint_factors` is a helper
lemma. Let `K` be an algebraically closed field, and let `H` be a group scheme
over `Spec K` with affine structure map, locally of finite type, and with
reduced underlying scheme. If `z : Z ⟶ H.X.left` is a closed immersion and
every rational point `g` of `H` has some `s : Spec K ⟶ Z` with
`s ≫ z = g.left`, then `z` is an isomorphism.

Proof. `H.X.left` is affine, so by Mathlib's
`IsClosedImmersion.isIso_of_injective_of_isAffine` it suffices that
`z.appTop : Γ(H.X.left, ⊤) ⟶ Γ(Z, ⊤)` is injective. Let `z.appTop a =
z.appTop b`. The published
`Langlands.GroupScheme.CentralIntersection.eq_zero_of_forall_evalPoint_eq_zero`
(`Langlands.GroupScheme.Derived.CentralIntersection.Unipotence`) says that on
such an `H` a global function vanishing at every rational point is zero.
Apply it to `a - b`. For a rational point `g`, write `g.left = s ≫ z`. Then
`evalPoint g (a - b)` is the image under `Scheme.ΓSpecIso` of
`s.appTop (z.appTop (a - b)) = s.appTop 0 = 0`. Hence `a - b = 0`.

## The two implications

- If `G` is unipotent, then `G_K` is unipotent by
  `unipotentFieldExtensionStatement k K G`. The first part of
  `perfectFieldUnipotentRationalPoints K G_K` then gives
  `IsNilpotent ((ρ.rationalMatrix g : Matrix n n K) - 1)` for every
  `n : Type` with `[Fintype n] [DecidableEq n]`, every matrix representation
  `ρ` of `G_K` and every `K`-point `g` of `G_K`.
- Conversely, suppose every such `ρ.rationalMatrix g` is unipotent. The
  helper lemma, applied to `H = G_K`, supplies the schematic-density
  hypothesis of the second part of `perfectFieldUnipotentRationalPoints K G_K`.
  That part gives `IsUnipotent G_K`. Then `unipotentFieldReflection k K G`
  gives `IsUnipotent G`.

## Scope

The theorem uses only the hypotheses of the statement. Connectedness is not
assumed, and none of the published results used needs it. Smoothness is used
only to make `G_K` reduced and locally of finite type. Affineness is used for
the field-extension results, for the 14.10 proof, and to make `G_K.X.left`
affine in the density lemma. Over `k`, local finite type comes from
smoothness.
