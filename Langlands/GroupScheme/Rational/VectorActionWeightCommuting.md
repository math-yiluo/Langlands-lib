# Linearity of vector actions commuting with a nonzero split-torus weight

Author: Worker 1045.

This internal module proves, in every characteristic, that an actual action
on a vector group which commutes with a split-torus action of one nonzero
weight `χ` is scalar linear in every system of weight-`χ` vector coordinates.
The Library previously had the upgrade from coefficient-algebra linearity to
all-test linearity (`IsAffineLinearVectorCoordinates.isLinearVectorCoordinates`,
module `Langlands.GroupScheme.Rational.VectorActionCharZero`), but no criterion
for linearity of an action that is not itself a torus action, outside
characteristic zero. All statements hold at an arbitrary universe `u`.

## Setting

Let `k` be a field, `S` a commutative group scheme over `Spec k`, and `H`, `V`
group schemes over `Spec k`. Vector coordinates on `V` are a family of group
isomorphisms

```text
e T : (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))
```

for every test scheme `T` over `Spec k`. For a `k`-algebra `A`,
`Lie.AffinePoints H A` denotes the `A`-points of `H`, and
`vectorAffineCoordinates e A` is the published transport of `e` to `A`-points,
with values in `Fin d → A`.

The published predicates used are (module
`Langlands.GroupScheme.Rational.WeightSemigroupStatement` and
`Langlands.GroupScheme.Rational.CentralVectorQuotientStatement`):

- `IsWeightVectorCoordinates c χ e`, for `c : AutomorphicAction S.toGrp V`:
  `e` is natural in `T`, and `e T (c.act s v) = χ(s) • e T v`.
- `IsLinearVectorCoordinates b e`, for `b : AutomorphicAction H V`: `e` is
  natural in `T`, and for every `h : T ⟶ H.X` and every `c ∈ Γ(T.left, ⊤)` the
  map `x ↦ e T (b.act h (e T ⁻¹ x))` commutes with multiplication by `c`.
- `IsAffineLinearVectorCoordinates b e`: the same scalar linearity, only for
  `A`-points over `k`-algebras `A` in the coordinates `vectorAffineCoordinates e A`.

## Declarations

In namespace `Langlands.GroupScheme.RelativeRoot`:

- `pointsEquiv_cocharacter_comp_character hD T u`: if
  `latticePairing S χ ζ = D` for a natural number `D`, then the character `χ`
  takes the value `u ^ D` at the torus point `ζ(u)`, for every unit `u` of
  `Γ(T.left, ⊤)`.
- `IsWeightVectorCoordinates.vectorAffineCoordinates_act he s v`: for weight
  coordinates, an `A`-point `s` of `S` scales the coordinates of an `A`-point
  `v` by the value of `χ` at `s`, read in `A` through `Scheme.ΓSpecIso`.
- `coordinateAffineAction b e h x` (definition): for an `A`-point `h` of `H`
  and `x : Fin d → A`, the coordinates of `b.act h` applied to the point with
  coordinates `x`. Its basic properties are additivity
  `coordinateAffineAction_add`, naturality in `k`-algebra maps `f : A →ₐ[k] B`
  (`coordinateAffineAction_naturality`, for natural `e`), and
  `coordinateAffineAction_weight_smul`: if `b` and `c` commute pointwise on
  every test scheme, then `coordinateAffineAction b e h` commutes with scaling
  by the value of `χ` at any `A`-point of `S`.
- `laurentCAlgHom A : A →ₐ[k] A[T;T⁻¹]`, the constant coefficients, and
  `laurentPowerAlgHom A D : A[X] →ₐ[k] A[T;T⁻¹]`, the substitution `X ↦ t ^ D`;
  `laurentPowerAlgHom_injective A hD` proves injectivity for `0 < D`.
- `isUnit_laurentT_global A` and `laurentCocharacterPoint A ζ`: the unit `t` of
  `Γ(Spec A[t, t⁻¹], ⊤)` and the torus point `ζ(t)`;
  `laurentCocharacterPoint_value hD` says that `χ(ζ(t)) = t ^ D` in
  `A[t, t⁻¹]` when `latticePairing S χ ζ = D`.
- `coordinateAffineAction_smul hS hχ he hbc h a x` (**main computation**):
  for `hS : IsSplitTorus S.toGrp`, `hχ : χ ≠ 0`,
  `he : IsWeightVectorCoordinates c χ e` and `hbc` the pointwise commutation
  `b.act h (c.act s v) = c.act s (b.act h v)` on every test scheme,
  `coordinateAffineAction b e h (a • x) = a • coordinateAffineAction b e h x`
  for every `k`-algebra `A`, `A`-point `h`, `a : A` and `x : Fin d → A`.
- `isAffineLinearVectorCoordinates_of_commute hS hχ he hbc`: the conclusion
  `IsAffineLinearVectorCoordinates b e`.
- `isLinearVectorCoordinates_of_commute hS hχ he hbc` (needs
  `IsAffineHom H.X.hom`): the conclusion `IsLinearVectorCoordinates b e`.

## Proofs

1. `pointsEquiv_cocharacter_comp_character`: by the published
   `latticePairing_apply`, `ζ ≫ χ` is the endomorphism `D` of `Gm`
   (`gmEndEquiv`); composing points with it is the `D`-th power
   (`gmEndEquiv_symm_comp`).
2. `coordinateAffineAction_weight_smul`: the point with coordinates
   `χ(s) • y` is `c.act s` of the point with coordinates `y`
   (`vectorAffineCoordinates_act`); then apply `hbc` and
   `vectorAffineCoordinates_act` again.
3. `laurentPowerAlgHom_injective`: as a ring map, the substitution equals
   `Polynomial.toLaurent ∘ Polynomial.expand A D` (checked on constants and on
   `X`), and both factors are injective (`Polynomial.toLaurent_injective`,
   `Polynomial.expand_injective`).
4. `coordinateAffineAction_smul`. The published
   `IsSplitTorus.exists_pairing_eq_pos` gives a cocharacter `ζ` with
   `⟨χ, ζ⟩ = D > 0`. Let `h'` be the image of `h` in `A[X]` and
   `P = coordinateAffineAction b e h' (X • x)`, a tuple of polynomials.
   - Mapping along `φ = laurentPowerAlgHom A D` sends `h'` to the constant image
     of `h` and `X • x` to `t ^ D • x`. By naturality, `φ(P)` is the action of
     the constant image of `h` on `t ^ D • x`.
   - By `coordinateAffineAction_weight_smul` at the torus point `ζ(t)`, whose
     `χ`-value is `t ^ D` (`laurentCocharacterPoint_value`), and naturality
     along the constants `A → A[t, t⁻¹]`, the same tuple equals
     `t ^ D • y`, where `y = coordinateAffineAction b e h x` viewed as constants.
   - Hence `φ(P_j) = φ(X * C (y_j))` for every `j`, and injectivity of `φ` gives
     `P_j = X * C (y_j)`.
   - Evaluating at `X = a` (the `k`-algebra map `A[X] → A`, `X ↦ a`, which sends
     `h'` back to `h` by `Lie.affineMap_comp` and `Lie.affineMap_id`), naturality
     gives `coordinateAffineAction b e h (a • x) = a • y`.
5. `isAffineLinearVectorCoordinates_of_commute` applies step 4 to the coordinates
   of `v`; `isLinearVectorCoordinates_of_commute` then applies the published
   upgrade `IsAffineLinearVectorCoordinates.isLinearVectorCoordinates` with the
   naturality part `he.1`.

## Provenance

Internal and derived. The notion of linearity is the Library's coordinate
expression `IsLinearVectorCoordinates` of an equivariant linear structure,
whose literature source (Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition, A.1.1 and B.4.3) is recorded in the published
`CentralVectorQuotientStatement` module. The linearity criterion and its proof
are internal: the substitution `X ↦ t ^ D` against a torus point of weight
`t ^ D` replaces the characteristic-zero doubling argument of the published
`VectorActionCharZero` module, so no restriction on the characteristic is
needed. No literature theorem is formalized here as stated.
