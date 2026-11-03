# Actions of `GL_n` from natural actions on affine points

Author: Worker 1399. Internal helper module for the proof of
`Langlands.GroupScheme.GeneralLinearSolvableStabilizerStatement`; it has no literature source.
It turns an action of the matrix groups `GL_n(A)` on the `A`-points of a scheme, natural in
the `R`-algebra `A`, into an actual `SchemeAction` of the Library's general linear group
scheme `Langlands.GroupScheme.GeneralLinear.groupScheme n (CommRingCat.of R)` over `Spec R`.

Namespace `Langlands.GroupScheme.GeneralLinear`; `n` is a finite type with decidable
equality and `R : Type u` a commutative ring. `specOver A`, `specMapOver φ`, `exists_over_hom`
and `over_hom_ext` are from `Langlands.AlgebraicGeometry.AffinePointGluing`.

## Matrices of affine points

- `matrixOf h : GL n A` for a point `h : specOver A ⟶ GL_n.X`: the Library's points
  equivalence `pointsEquiv n _ (specOver A) h : GL n Γ(Spec A, ⊤)` followed by the ring
  isomorphism `Γ(Spec A, ⊤) ≅ A` (`Scheme.ΓSpecIso`) applied to the entries.
- `matrixOf_injective`, `matrixOf_one`, `matrixOf_mul`: `matrixOf` is an injective group
  homomorphism for the pointwise group structure on points (from `pointsEquiv` being a
  multiplicative equivalence).
- `matrixOf_comp`: naturality,
  `matrixOf (specMapOver φ ≫ h) = GeneralLinearGroup.map φ (matrixOf h)` for
  `φ : A →ₐ[R] B`. Proof: entrywise from `pointsEquiv_comp_apply` and naturality of
  `Scheme.ΓSpecIso`.

## The scheme action

`exists_schemeAction_of_affine`: let `X : Over (Spec R)`, and let
`act A : GL n A → (specOver A ⟶ X) → (specOver A ⟶ X)` be given for every `R`-algebra `A`
(in universe `u`), with

- naturality `act B (GeneralLinearGroup.map φ g) (specMapOver φ ≫ x) = specMapOver φ ≫ act A g x`
  for every `φ : A →ₐ[R] B`,
- `act A 1 x = x`, and
- `act A (g * g') x = act A g (act A g' x)`.

Then there is `a : SchemeAction (groupScheme n (CommRingCat.of R)) X` with
`a.act h x = act A (matrixOf h) x` for every `R`-algebra `A`, every point `h` of `GL_n` and
every point `x` of `X` over `specOver A`. Here `a.act h x` is the Library's
`lift h x ≫ a.hom`.

Proof: the family `y ↦ act A (matrixOf (y ≫ fst)) (y ≫ snd)` on affine points of
`GL_n.X ⊗ X` is natural (by `matrixOf_comp` and the naturality hypothesis). Then
`exists_over_hom` gives a morphism `f : GL_n.X ⊗ X ⟶ X` over `Spec R` with
`lift h x ≫ f = act A (matrixOf h) x` on affine points. The Library constructor
`schemeActionOfPointLaws f` needs the identity and multiplication laws on all test schemes.
By `over_hom_ext` it suffices to check them on affine points. There they reduce to `hone` and
`hmul` through `comp_lift`, `MonObj.comp_one`, `MonObj.comp_mul`, `matrixOf_one` and
`matrixOf_mul`.

The theorem is applied in `Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof`
to the action of `GL_N(A)` on stable Grassmannian points.
