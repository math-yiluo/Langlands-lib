# The Mumford map of a diagonal Poincaré pullback at a point

Module `Langlands.AlgebraicGeometry.Picard.PoincareDiagonalClasses`.

## Setting

All declarations are in `Langlands.AbelianScheme`. The data are those of the target
statement `PolarizationDiagonalMumfordStatement`: an abelian scheme `A` over `S` with a dual
scheme (`hA`, `geometryA`, `MA`, `evaluationA`) and the constructor hypotheses
`preservation`, `stability`, `composition`, `unitCoherence`, `associativity`, `comparison`,
`symmetry`. `DA` denotes the dual abelian scheme `dualAbelianSchemeFromEvaluation …`, whose
underlying scheme is `dualScheme A hA`. `P` is the Poincaré family on `A^∨ ×_S A`. Classes
`[–]` are in `LineBundle.IsoClasses`, and `[P(z, x)]` is `familyPointClass … P z x`
(module `PoincarePointClasses`).

## Bilinearity of Poincaré classes

- `nonempty_relativePullback_poincareFamily_mul_iso`: for `u, u' : T ⟶ DA.X`, the pullback
  of `P` along `u * u'` is isomorphic to the tensor product of the pullbacks along `u` and
  `u'`. This is the multiplicativity of the Library's `dualAbelianSchemePointMulEquiv`
  (points of the dual ≃ rigidified Picard classes), read through `classifyingMap_eq_iff`.
- `familyPointClass_poincareFamily_mul_left`: `[P(u u', x)] = [P(u, x)] [P(u', x)]`.
- `familyPointClass_poincareFamily_mul_right` (uses `stability`):
  `[P(z, x y)] = [P(z, x)] [P(z, y)]`, from the Library's theorem of the square
  `nonempty_pullback_pairOver_mul_iso`, applied with the proved theorems
  `picardZeroLineBundleClassification` and `smoothProperConnectedGlobalFunctions`.

## Other auxiliary lemmas

- `isoClass_pullback_poincareDiagonalBundle`: for `f : A.X ⟶ dualScheme A hA` and a point
  `x`, the class of `x^* (1, f)^* P` (with `poincareDiagonalBundle` from the target module) is
  `[P(x f, x)]`.
- `isoClass_pullback_baseBundle_eq_one`, `pullbackHom_relativeFst_eq_one`: if `T.left` has
  exactly one point, then classes on `T ×_S A` that come from `S` or from `T` are trivial,
  since they factor through `T` (`LineBundle.pullbackHom_eq_one_of_factor`).
- `eq_of_nonempty_relativePullback_poincareFamily_iso` (uses `stability`): two points
  `u, v : T ⟶ dualScheme A hA` with isomorphic Poincaré pullbacks are equal, by the
  Library's `dualPointClass_injective` (universality of `P`).

## Main lemmas

Fix `lam0 : A.X ⟶ DA.X` with `[IsMonHom lam0]`, normalization data `B`, `evaluationB`, `M`,
`evaluation` for the line bundle `(1, lam0)^* P`, and `square`. Let `g` be its Mumford map
`mumfordSchemeMapOfLineBundle preservation A (poincareDiagonalBundle A hA lam0) … square hA`.
Let `t : T ⟶ A.X` with `T.left` having exactly one point, and assume
`PoincareSliceSymmetric A hA lam0 t`. On `T ×_S A` write `τ = pr₁ ≫ t` and `a = pr₂`.

- `familyPointClass_mumfordSchemeMap_poincareDiagonal`:
  `[P(τ g, a)] = [P(τ lam0, a)] · [P(τ lam0, a)]`.

  Proof. By `mumfordSchemeMapOfLineBundlePullbackIso` and
  `familyPointClass_mumfordFamily`, the left side is
  `[(τ a)^* ((1, lam0)^* P ⊗ π^* B)] · [τ^* M] · [a^* M]`. The factor from `B` and the
  factor `[τ^* M]` are trivial because they come from `S` or `T`. Since `lam0` is a monoid
  map, `(τ a) lam0 = (τ lam0)(a lam0)`, and bilinearity gives
  `[(τ a)^* (1, lam0)^* P] = [P(τ lam0, τ)] [P(τ lam0, a)] [P(a lam0, τ)] [P(a lam0, a)]`.
  Here `[P(τ lam0, τ)] = 1` (it comes from `T`), and `[P(a lam0, τ)] = [P(τ lam0, a)]` is the
  slice symmetry. Finally `[P(a lam0, a)] · [a^* M] = 1`: pull back the isomorphism
  `(1, lam0)^* P ⊗ π^* B ⊗ M ≅ 𝒪` (`evaluation`) along `a`, where `a` is the identity of `A`
  base-changed to `T`.
- `comp_mumfordSchemeMap_poincareDiagonal`: `t ≫ g = (t ≫ lam0) * (t ≫ lam0)`.

  Proof. By `eq_of_nonempty_relativePullback_poincareFamily_iso` it suffices to compare the
  Poincaré pullbacks along both sides. The pullback along the right side is the tensor square
  of the pullback along `t ≫ lam0` (`nonempty_relativePullback_poincareFamily_mul_iso`). The
  underlying line bundles have equal classes by the previous lemma (evaluated at the
  tautological point via `isoClass_forget_eq_familyPointClass` and
  `familyPointClass_relativePullback`). The Library's
  `RigidifiedLineBundle.nonempty_iso_of_forget_iso` turns the isomorphism of underlying
  bundles into an isomorphism of rigidified families.

## Provenance and purpose

Internal steps of the proof of `Langlands.AbelianScheme.PolarizationDiagonalMumfordStatement`
(Mumford, Fogarty, Kirwan, *Geometric Invariant Theory*, 3rd ed., Prop. 6.10). GIT's proof
instead uses `(1, λ)^* P ≅ [2]^* L ⊗ L^{-2}` over an algebraically closed field and the
algebraic equivalence of `[2]^* L` and `L^4`. The computation here is an alternative: by
bilinearity of the Poincaré bundle, `Λ((1, λ)^* P)(t)` is `λ(t)` plus the transposed slice
term at `t`, which equals `λ(t)` by the slice symmetry. It is carried out only at points over
one-point schemes, where line bundles coming from the parameter scheme are trivial.
