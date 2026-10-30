# The theorem of the square for line bundles on abelian group schemes over a field

This module states, as the Prop-valued definition
`Langlands.GroupScheme.FieldTheoremOfTheSquareStatement`, Milne's theorem of the square
(Theorem 6.7) for actual line bundles and rational translations. It is a statement
target: no proof is supplied.

## The statement

For every universe `u`, every field `K : Type u`, and every group object
`G : Grp (Over (Spec K))` with `[IsCommMonObj G.X]`, assume exactly `Smooth G.X.hom`,
`IsProper G.X.hom` and `GeometricallyConnected G.X.hom`. Then for every actual line
bundle `L : LineBundle G.X.left` and all rational points
`a b : Over.mk (𝟙 (Spec K)) ⟶ G.X` there is an isomorphism of module sheaves on
`G.X.left`

```
tensorObj (Q (a * b)) L.obj ≅ tensorObj (Q a) (Q b),
```

where `Q c` is `(Scheme.Modules.pullback (translation G c).left).obj L.obj`, the pullback
of `L` along translation by `c`. The conclusion is `Nonempty` of this isomorphism.

- `LineBundle X` (`Langlands.AlgebraicGeometry.Picard.LineBundle`) is the full
  subcategory of locally free rank-one module sheaves on `X`; `L.obj` is the
  underlying module sheaf.
- `translation G c` is the published left translation in
  `Langlands.AlgebraicGeometry.Picard.GeometricPicardZero`, built from the actual group
  law. By `points_translation` it sends a point `y` to `c * y`, so it is Milne's
  `t_c : x ↦ x + c`. By `translation_one` translation by the identity is `𝟙 G.X`.
- `Scheme.Modules.pullback` is Mathlib's pullback functor of module sheaves
  (`AlgebraicGeometry.Scheme.Modules.pullback`; the Lean source writes the
  root-qualified name).
- The product `a * b` of points is the group law of `G` on rational points. Since `G` is
  commutative it is Milne's sum `a + b`.
- `tensorObj` is the published tensor product of module sheaves
  (`Langlands.Scheme.Modules.tensorObj`). Each side has exactly two factors.

Algebraic closure, characteristic restrictions, the theorem of the cube, fibrewise
triviality, Picard-zero or translation-invariance hypotheses, isomorphism certificates,
projectivity and ampleness are not premises. The universe, the characteristic of `K`
and the dimension of `G` (including dimension zero) are unrestricted.

## Source

J. S. Milne, *Abelian Varieties* (corrected author version, January 2, 2022; registered
as `milne-abelian-varieties-1986-author-2022`), Section 6, pp.8–10. The retained errata
(`milne-abelian-varieties-1986-errata-2026-10-25`) says its corrections are
incorporated in that version and none concerns Sections 6 or 7.

- **Conventions (pp.2–3).** Milne works over an arbitrary field `k`. A variety is a
  separated scheme of finite type whose base change to `k̄` is integral, an abelian
  variety is a complete connected group variety, `t_a` is the translation
  `P ↦ m(a, P)`, and the group law is commutative (Corollary 2.4) and written
  additively. `A(k)` denotes the `k`-rational points.
- **Theorem 6.7 (Theorem of the square, p.10).** For all invertible sheaves `L` on an
  abelian variety `A` and points `a, b ∈ A(k)`,
  `t_{a+b}^* L ⊗ L ≅ t_a^* L ⊗ t_b^* L`. Milne proves it by applying Corollary 6.5
  (p.9) with `f` the identity and `g`, `h` the constant maps with images `a`, `b`. The
  theorem of the cube (6.1) behind it is proved over an arbitrary field `k` (Lemma 6.2
  reduces to the algebraically closed case), and the points are `k`-rational. This
  matches the absence of algebraic closure here. Printed Corollary 6.5 omits the
  inverse on the `(f+h)` factor. The intended formula, following the three inverse pair
  factors of Corollary 6.4, gives exactly the two-factor isomorphism above.
- **Remark 6.8 (p.10).** Tensoring with `L⁻²` gives
  `t_{a+b}^* L ⊗ L⁻¹ ≅ (t_a^* L ⊗ L⁻¹) ⊗ (t_b^* L ⊗ L⁻¹)`. So `a ↦ t_a^* L ⊗ L⁻¹` is a
  homomorphism `A(k) → Pic(A)`, and `∑ aᵢ = 0` implies
  `t_{a₁}^* L ⊗ ⋯ ⊗ t_{aₙ}^* L ≅ Lⁿ`.
- **Remark 6.9 (p.10).** Writing `∼` for linear equivalence and `D_a = t_a D = D + a`
  for the translate, Milne notes `t_a^* L(D) = L(t_a⁻¹ D) = L(D − a)`. Then 6.7 and 6.8
  become `D_{a+b} + D ∼ D_a + D_b` and `∑ D_{aᵢ} ∼ nD` when `∑ aᵢ = 0`. With the present
  convention `Q c = t_c^* L`, the pullback along `x ↦ c * x`, a section of `L` vanishing
  on `D` pulls back to a section of `Q c` vanishing on `D − c`.

## Lean correspondence

`Q (a * b) ⊗ L ≅ Q a ⊗ Q b` is Theorem 6.7 with `t_a^* L` read as `Q a`. The statement is
in the form Milne prints, with no inverse bundles. Milne's abelian varieties correspond
to the hypotheses on `G`: smooth (so geometrically regular, hence geometrically reduced),
proper (so separated, of finite type and complete) and geometrically connected (so, for
a smooth group scheme, geometrically integral). Commutativity, a theorem in Milne
(Corollary 2.4), is assumed through `IsCommMonObj G.X` so that `a * b` is the additive
sum. Rational points `a ∈ A(k)` are morphisms from the terminal object
`Over.mk (𝟙 (Spec K))`. Invertible sheaves are actual locally free rank-one module
sheaves, and `≅` is an isomorphism of module sheaves, not an equality of classes in a
Picard group.

## Intended use

The separating-section construction for parent task
`eda1f6ff-d036-4f23-aabb-7663e7606b42` (target
`Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement`; Milne, proof of
Theorem 7.1, p.11) needs the three-translate consequence for the points `a`, `b`,
`(a * b)⁻¹`, i.e. `a`, `b`, `−a−b`: `Q a ⊗ Q b ⊗ Q ((a * b)⁻¹) ≅ L ⊗ L ⊗ L`. It would
follow by applying this statement to `a, b` and to `a * b, (a * b)⁻¹`, together with
`translation_one` and the associativity and symmetry of `tensorObj`. That consequence is
not stated or proved here.

Provenance: a direct formalization of Theorem 6.7 for group schemes over a field
satisfying the stated hypotheses.
