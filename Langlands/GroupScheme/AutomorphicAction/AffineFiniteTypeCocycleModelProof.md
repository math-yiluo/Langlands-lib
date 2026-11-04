# Existence of an affine finite-type cocycle model: proof

Authors: Worker 1412 (this module and its helper modules) and Worker 1076 (the imported
general linear coordinates and finite-family basis lemma).

The theorem
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelProof.affineFiniteTypeCocycleModel.{u}`
has type exactly
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement.{u}`,
imported unchanged from [AffineFiniteTypeCocycleModelStatement](AffineFiniteTypeCocycleModelStatement.md).
Let `k : Type u` be any field, `H` and `G` group schemes over `Spec k` whose structure
morphisms are affine and locally of finite type, and `a` an automorphic action of `H` on
`G`. The theorem produces an `a.CocycleModel` `M` with `M.scheme.hom` affine and
locally of finite type. It adds no hypothesis and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The route follows the proof of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd
edition (2015), Lemma A.8.13 (printed pp.553–554). Embed `G ⋊ H` in a general linear
group, so that cocycles become sections of `G × H → H` with coordinates in an affine
space. The sections whose coordinates lie in one fixed finite-dimensional space of
functions on `H` form a closed, hence affine finite-type, subfunctor of an affine space.
That space is chosen to contain the coordinates of the trivial cocycle, and it is
stable under conjugation by `G`, which acts on the coordinates through conjugation of
matrices. The implementation works with actual morphisms and arbitrary test schemes
throughout, so no gluing argument is needed.

## Modules

- [PolynomialSpecPoints](../../AlgebraicGeometry/PolynomialSpecPoints.md): points of
  the affine space `space R K` and their coordinates `coord`, `mk`.
- [ProductCoefficientInjectivity](../../AlgebraicGeometry/ProductCoefficientInjectivity.md):
  uniqueness of coefficients along a linearly independent family of functions on an
  affine factor of a product over a field.
- [ClosedLiftingLocus](../../AlgebraicGeometry/ClosedLiftingLocus.md): closed loci of
  liftings and of equalities, from the Library's closed factorization locus theorem.
- [SectionCoordinateModel](SectionCoordinateModel.md): the closed subscheme `Z` of
  `𝔸^{C × m}` with universal cocycle `U`, realization criterion and injectivity
  (`exists_model`).
- Published Library modules by Worker 1076 (with Worker 1412):
  `Langlands.GroupScheme.GeneralLinearAffineCoordinates` (the closed embedding `toSpace`
  of `GL_n` into the affine space of matrix and inverse-matrix entries, and the
  conjugation formulas `values_conj`, `conjCoords_sum_mul`, `conjCoords_map`), and
  `Langlands.LinearAlgebra.FiniteFamilyBasis`
  (`exists_linearIndependent_sum_algebraMap_mul`).
- The Library's closed linear embedding theorem `affineLinearEmbeddingStatement`
  (`Langlands.GroupScheme.AffineLinearEmbeddingProof`), the semidirect product
  `a.semidirectProduct` with its point description, and `schemeActionOfPointLaws`.

## Declarations of this module

All are in `Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelProof`.

- `finite_coordinate` (instance): the type `GeneralLinear.Coordinate n` of matrix and
  inverse-matrix entries is finite when `n` is.

### A cocycle model from a conjugation-stable family

Fix a base scheme `S`, group schemes `H G` over `S`, an action `a`, `Z : Over S` and
`U : a.Cocycle Z`. Suppose `hconj`: for every `T`, `g : T ⟶ G.X` and `x : T ⟶ Z` there is
`x' : T ⟶ Z` with `restrict x' U = conjugate g (restrict x U)`.

- `conjugationHom U hconj : G.X ⊗ Z ⟶ Z` is such an `x'` chosen (by `Classical.choose`)
  for the universal case `T = G × Z`, `g = fst`, `x = snd`.
- `restrict_lift_conjugationHom`: for all `g`, `x`,
  `restrict (lift g x ≫ conjugationHom U hconj) U = conjugate g (restrict x U)`. This
  follows from the universal case by `restrict_comp` and `restrict_conjugate`.
- `modelOfConjugate U hinj hconj x₀ hx₀ : a.CocycleModel` assumes in addition that
  `x ↦ restrict x U` is injective on every `T` (`hinj`) and that
  `x₀ : 𝟙_ (Over S) ⟶ Z` has `restrict x₀ U = trivial` (`hx₀`). Its scheme is `Z`, its
  universal cocycle `U`, its basepoint `x₀`. Its action is
  `schemeActionOfPointLaws (conjugationHom U hconj)`. The identity and associativity laws
  hold because, by injectivity, they reduce to `Cocycle.conjugate_one` and
  `Cocycle.conjugate_mul`. Equivariance is `restrict_lift_conjugationHom`.

### Embedding over a field

Now let `k` be a field, `H G` group schemes over `Spec k`, `a` an action, and
`ρ : MatrixRepresentation a.semidirectProduct (Fin N)`. The underlying object of
`a.semidirectProduct` is `G.X ⊗ H.X`.

- `locallyOfFiniteType_tensor`: a fibre product over `Spec k` of two objects that are
  locally of finite type is locally of finite type.
- `toSemidirect a f` (abbrev) regards `f : V ⟶ G.X ⊗ H.X` as a point of
  `a.semidirectProduct`.
- `embedding a ρ : G.X ⊗ H.X ⟶ space k (Coordinate (Fin N))` is `ρ.hom.hom ≫ toSpace`.
- `coord_embedding`: the coordinates of `w ≫ embedding a ρ` are
  `values (ρ.pointMatrix V (toSemidirect a w))`, the entries of the matrix of `w` and of
  its inverse. Proof: `toSpace_appTop` after reassociating.
- `graph a ρ = lift (snd G.X H.X) (embedding a ρ) : G.X ⊗ H.X ⟶ H.X ⊗ space k (Coordinate (Fin N))`,
  with `graph_fst : graph a ρ ≫ fst = snd G.X H.X`.
- `isClosedImmersion_graph`: if `H.X.hom` is affine and `ρ` is a closed subgroup
  (`IsClosedSubgroup ρ`), then `(graph a ρ).left` is a closed immersion. Composing it
  with the separated projection `snd` gives `embedding`, the closed immersion
  `ρ.hom.hom.left` followed by the closed immersion `toSpace`. So
  `IsClosedImmersion.of_comp` applies.
- `sec_conjugate`: for `g : T ⟶ G.X` and `c : a.Cocycle T`, the section of the
  conjugate cocycle is the conjugate of the section in the semidirect product:
  `sec (conjugate g c) = γ * sec c * γ⁻¹` with `γ = (snd H.X T ≫ g) ≫ semidirectInl`.
  Proof: compare `G`- and `H`-components through `semidirectPointsEquiv`; the
  `G`-component is `Cocycle.eval_conjugate`, and both `H`-components are `fst H.X T`.
- `sec_trivial`: `sec (trivial T) = fst H.X T ≫ lift 1 (𝟙 H.X)`.

### Conjugation and the basepoint in coordinates

Let `e : Fin m → Γ(H.X.left, ⊤)`, `Z`, `i : Z ⟶ space k (Coordinate (Fin N) × Fin m)`
and `U : a.Cocycle Z` satisfy the realization criterion `hreal` of
`SectionCoordinateModel.exists_model` for `j = graph a ρ`. That is, `y` and `c` come
from a point of `Z` exactly when `(H.X ◁ y) ≫ lift fst (Φ H.X _ e) = sec c ≫ graph a ρ`.

- `exists_conjugate`: for `g : T ⟶ G.X` and `x : T ⟶ Z` there is `x' : T ⟶ Z` with
  `restrict x' U = conjugate g (restrict x U)`. Proof. Put
  `U_T = ρ.pointMatrix T (g ≫ semidirectInl)` and let `y'` be the point whose
  `(κ, l)`-coordinate is the `κ`-entry of `conjCoords U_T (coord (x ≫ i) (·, l))`. This
  conjugates each coefficient matrix by `U_T`. By `hreal` for `x` and
  `coord_embedding`, the matrix entries of `sec (restrict x U)` are
  `∑ l, fst^*(e l) * snd^*(coord (x ≫ i) (κ, l))`. By `sec_conjugate`, `values_conj`,
  `conjCoords_sum_mul` and the naturality of `pointMatrix` and of `conjCoords` under
  ring maps (`conjCoords_map`), the entries of the conjugate section are the same
  expression with the coefficients of `y'`. So `hreal` (backwards) gives `x'`.
- `exists_trivial`: suppose `r : Coordinate (Fin N) → Fin m → k` expresses the
  coordinates of the canonical section `lift 1 (𝟙 H.X) ≫ embedding a ρ` as
  `∑ l, (scalar r κ l) * e l`, where the scalar is the image of `r κ l` under
  `Γ(Spec k) → Γ(H)`. Then the constant point `y₀` of `𝔸^{C × m}` over the unit object
  with coordinates `r` satisfies the criterion for the trivial cocycle, by
  `sec_trivial`. Pulled back to `H × 𝟙`, the scalars agree on both factors because both
  structure morphisms factor through `Spec k`. This gives `x₀` with
  `restrict x₀ U = trivial`.

### Assembly

In `affineFiniteTypeCocycleModel`, `a.semidirectProduct` is affine and locally of
finite type (`locallyOfFiniteType_tensor`). So `affineLinearEmbeddingStatement` gives
`ρ` with `IsClosedSubgroup ρ`. Using the `k`-algebra structure
`Scheme.TwoAffineOpenCover.algebraOfHom H.X.hom ⊤` on `Γ(H)`,
`exists_linearIndependent_sum_algebraMap_mul` expresses the finitely many coordinates
of the canonical section through a linearly independent family `e` with coefficients
`r`. Then `exists_model` (with `C = Coordinate (Fin N)` and `j = graph a ρ`) gives
`Z, i, U` with the realization criterion and injectivity. `exists_trivial` gives the
basepoint and `exists_conjugate` gives `hconj`, so `modelOfConjugate` is a cocycle
model. Its scheme `Z` has a closed immersion into the finite affine space
`space k (Coordinate (Fin N) × Fin m)`. Hence `Z.hom` is affine and locally of finite
type (`isAffineHom_of_isClosedImmersion`, `locallyOfFiniteType_of_isClosedImmersion`).
