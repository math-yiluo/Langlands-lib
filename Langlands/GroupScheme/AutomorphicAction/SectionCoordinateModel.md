# Cocycles whose sections have coordinates linear in a fixed family

Author: Worker 1412.

This module is an internal helper for the proof of
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement`
(see [AffineFiniteTypeCocycleModelProof](AffineFiniteTypeCocycleModelProof.md)).
It constructs a closed subscheme `Z` of an affine space that parametrizes cocycles
of a particular shape, through a universal cocycle, injectively on every test scheme.
The construction follows the idea of the proof of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, 2nd edition (2015), Lemma A.8.13. There a cocycle is viewed
as a section of `G ⋊ H → H`, and the sections whose coordinates lie in a fixed
finite-dimensional space of functions form a closed subfunctor of an affine space. The
statements below are derived, internal formulations of that step. Conjugation and the
trivial cocycle are handled in the main proof module.

All declarations are in `Langlands.GroupScheme.AutomorphicAction.SectionCoordinateModel`.
Objects live in `Over S`, or in `Over (Spec R)` for coordinates, with the cartesian
monoidal structure (`⊗` is the fibre product over the base). `space R K` and `coord`
are from [PolynomialSpecPoints](../../AlgebraicGeometry/PolynomialSpecPoints.md).

## Sections attached to cocycle-shaped morphisms

For group schemes `H G` over `S` and `T : Over S`:

- `secHom d`, for `d : T ⊗ H.X ⟶ G.X`, is the morphism `H.X ⊗ T ⟶ G.X ⊗ H.X`,
  `(h, t) ↦ (d(t, h), h)`, i.e. `lift (lift (snd H.X T) (fst H.X T) ≫ d) (fst H.X T)`.
- `secHom_snd`: `secHom d ≫ snd G.X H.X = fst H.X T`, so `secHom d` is a section of the
  projection `G × H → H` over `H × T`.
- `secHom_fst`: `d` is recovered from `secHom d` by swapping the factors and projecting
  to `G`. Hence `secHom_injective`: `secHom d = secHom d'` implies `d = d'`.
- `sec c` (abbrev), for an automorphic action `a` of `H` on `G` and `c : a.Cocycle T`,
  is `secHom c.hom`.
- `secHom_whiskerRight`: if `σ : H.X ⊗ Z ⟶ G.X ⊗ H.X` satisfies
  `σ ≫ snd G.X H.X = fst H.X Z`, then for `z : T ⟶ Z` the morphism `secHom` of
  `(z ▷ H.X) ≫ lift (snd Z H.X) (fst Z H.X) ≫ σ ≫ fst G.X H.X` equals `(H.X ◁ z) ≫ σ`.
  So the cocycle-shaped morphism read off from a section pulls back along test maps.

## Linear coordinates

Fix `R : CommRingCat.{u}`, `X : Over (Spec R)`, a type `C`, `m : ℕ` and
`e : Fin m → Γ(X.left, ⊤)`.

- `Φ X C e : X ⊗ space R (C × Fin m) ⟶ space R C` is the morphism with coordinates
  `κ ↦ ∑ l, fst^*(e l) * snd^*(X_{(κ, l)})`. In words, `(x, y) ↦ (∑ₗ e_l(x) y_{κ,l})_κ`.
- `coord_whiskerLeft_Φ`: for a test point `y : T ⟶ space R (C × Fin m)`, the
  `κ`-coordinate of `(X ◁ y) ≫ Φ X C e` is
  `∑ l, (fst X T).left.appTop (e l) * (snd X T).left.appTop (coord y (κ, l))`.
- `appTop_comp`: `(f ≫ g).left.appTop x = f.left.appTop (g.left.appTop x)` for
  morphisms in `Over (Spec R)`.
- `isAffineHom_of_isClosedImmersion` and `locallyOfFiniteType_of_isClosedImmersion`:
  if `i : Z ⟶ space R K` has `i.left` a closed immersion, then `Z.hom` is affine, and
  it is locally of finite type when `K` is finite. Indeed, `Z.hom = i.left ≫ (space R K).hom`.

## The model over a field

From now on `k : Type u` is a field, and `H G` are group schemes over `Spec k` with an
automorphic action `a`.

- `isAffineHom_tensor`: the fibre product of two objects with affine structure
  morphisms has affine structure morphism.
- `MulLaw c₀ t`, for `c₀ : Z ⊗ H.X ⟶ G.X` and `t : T ⟶ Z`, says that the cocycle
  multiplication law
  `lift (b ≫ t) (h * h') ≫ c₀ = (lift (b ≫ t) h ≫ c₀) * a.act h (lift (b ≫ t) h' ≫ c₀)`
  holds for all `V`, `b : V ⟶ T` and `h h' : V ⟶ H.X`.
- `exists_mulLaw_locus` (with `H.X.hom` and `G.X.hom` affine): there are `Z₁` and a
  closed immersion `i : Z₁ ⟶ Z` such that `t` factors through `i` exactly when
  `MulLaw c₀ t`. Proof: apply `exists_equalizer_locus` from
  [ClosedLiftingLocus](../../AlgebraicGeometry/ClosedLiftingLocus.md) to `X = H × H`,
  which is affine by `isAffineHom_tensor`. Use the two morphisms
  `f₁, f₂ : (H × H) × Z ⟶ G` that are the two sides of the multiplication law at the
  universal point; `G` is separated because it is affine. Evaluating `(H × H) ◁ t`
  composed with `f₁` and `f₂` at a point `lift (lift h h') b` gives the two sides of the
  law (`e₁`, `e₂`). For the converse, evaluate at the identity point of `(H × H) × T`.

`exists_model C m j hj hjf e he` is the main result. Assume `H.X.hom` and `G.X.hom`
are affine. Let `j : G.X ⊗ H.X ⟶ H.X ⊗ space k C` be a morphism with `j.left` a closed
immersion and `j ≫ fst = snd G.X H.X`, so `j` is a closed embedding of `G × H` into
`H × 𝔸^C` over `H`. Let `e : Fin m → Γ(H.X.left, ⊤)` be linearly independent over `k`,
for the Library algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom H.X.hom ⊤`.
Then there exist `Z`, `i : Z ⟶ space k (C × Fin m)` with `i.left` a closed immersion
and a cocycle `U : a.Cocycle Z` such that:

- (realization) for every test `T`, every `y : T ⟶ space k (C × Fin m)` and every
  `c : a.Cocycle T`, there is `x : T ⟶ Z` with `x ≫ i = y` and
  `Cocycle.restrict x U = c` if and only if
  `(H.X ◁ y) ≫ lift (fst _ _) (Φ H.X C e) = sec c ≫ j`. That is, the section of `c`,
  embedded by `j`, has `𝔸^C`-coordinates `∑ₗ e_l · y_{κ,l}`;
- (injectivity) for every `T`, `x ↦ Cocycle.restrict x U` is injective on `T ⟶ Z`.

Proof. First, `exists_lifting_locus` (applied to `X = H`, `Y = 𝔸^{C × m}`, the closed
immersion `j` and `Ψ = lift fst (Φ H.X C e)`) gives a closed `i₀ : Z₀ ⟶ 𝔸^{C × m}`.
Its universal point yields `σ₀ : H.X ⊗ Z₀ ⟶ G.X ⊗ H.X` with `σ₀ ≫ j = (H.X ◁ i₀) ≫ Ψ`.
Since `j ≫ fst = snd`, `σ₀` is a section of `G × H → H`. Let `c₀ : Z₀ ⊗ H.X ⟶ G.X` be
its `G`-component with the factors swapped. Then `exists_mulLaw_locus c₀` gives a closed
`i₁ : Z ⟶ Z₀`. The universal cocycle is `U.hom = (i₁ ▷ H.X) ≫ c₀`. Its multiplication
law is `MulLaw c₀ i₁`. The normalization law `lift b 1 ≫ U.hom = 1` follows from the
multiplication law with `h = h' = 1`, because `x = x * x` forces `x = 1` in a group.
The model is `i = i₁ ≫ i₀`, a composition of closed immersions.

For realization in the forward direction, `secHom_whiskerRight` identifies `sec` of
`restrict x U` with `(H.X ◁ (x ≫ i₁)) ≫ σ₀`; composing with `j` gives the required
identity. Conversely, the identity makes `sec c` a lift of `(H.X ◁ y) ≫ Ψ` through `j`.
So `y` factors through `i₀` by some `z₀`. Since `j` is a monomorphism (a closed
immersion), `(H.X ◁ z₀) ≫ σ₀ = sec c`, and `secHom_injective` gives
`(z₀ ▷ H.X) ≫ c₀ = c.hom`. The multiplication law of `c` then shows `MulLaw c₀ z₀`, so
`z₀` factors through `i₁` by some `x`, and `restrict x U = c`.

For injectivity, suppose `restrict x U = restrict x' U`. Realization gives equal
morphisms `(H.X ◁ (x ≫ i)) ≫ Φ H.X C e = (H.X ◁ (x' ≫ i)) ≫ Φ H.X C e`. Compare the
`κ`-coordinates with `coord_whiskerLeft_Φ`.
`ProductCoefficients.coefficients_injective`
([ProductCoefficientInjectivity](../../AlgebraicGeometry/ProductCoefficientInjectivity.md))
applies because `H` is affine over `k` and `e` is linearly independent, and it shows
`coord (x ≫ i) (κ, l) = coord (x' ≫ i) (κ, l)` for all `κ, l`. Hence `x ≫ i = x' ≫ i` by
`PolynomialSpecPoints.ext`, and `x = x'` because the closed immersion `i` is a
monomorphism in `Over (Spec k)`.
