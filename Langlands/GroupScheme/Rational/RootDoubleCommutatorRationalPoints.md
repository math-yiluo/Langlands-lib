# Rational points detect the commutator pairing of a multipliable relative root

Let `k` be a field, `i : S → G` a split torus in a smooth affine `k`-group, and `a` a nonzero
relative root such that no `n • a` with `n ≥ 3` is a relative root. Let `U` and `U₂` represent
the root subgroups of `a` and `2 • a`, and let `C` be a commutator pairing
`DoubleRootCommutatorPairing i a hj hj₂` with quotient `C.V = U / U₂`. In the Library's
bilinear coordinates the commutator pairing `C.pairing : C.V × C.V → U₂` is bilinear
(`DoubleRootCommutatorPairing.exists_bilinear_coordinates`). The coordinate basis vectors are
rational, so a bilinear pairing that vanishes on rational points vanishes over every test
scheme. This module draws two consequences:

- if the rational points of `U` commute, then the points of `U` over every test scheme
  commute (`HeisenbergNormalForm.commute_of_commute_rationalPoints`);
- consequently, if two points of `U` over some test scheme do not commute, the cocycle of a
  Heisenberg normal form, read in coordinates of the rational points, is not symmetric
  (`HeisenbergNormalForm.exists_form_ne_swap`).

The second statement has the exact shape of the fields `first`, `second`, `form`,
`cocycle_eq` and `form_nonsymm` of `HeisenbergUnitaryData`
(`Langlands.Geometry.Building.RootUnitaryHeisenbergAssembly`). It reduces `form_nonsymm` to the
existence of two noncommuting points of `U` over some test scheme, for example over
`Spec L` for a splitting field `L`. This module does not produce such points.

Provenance: internal. The argument is elementary linear algebra on the Library's bilinear
coordinates. No literature source states these lemmas in this form.

All declarations live in namespace `Langlands.GroupScheme.RelativeRoot`.

## Definition

- `PointsCommute H`, for a group scheme `H` over `Spec k`: for every test scheme `T` over
  `Spec k`, any two `T`-points of `H` commute. That is,
  `∀ (T : Over (Spec k)) (g g' : T ⟶ H.X), Commute g g'`.

## Bilinear pairings of vector groups

Here `e` and `e'` are vector coordinates of `k`-group schemes `V` and `W`: for every test
scheme `T`, `e T` identifies the `T`-points of `V` with `Fin d → Γ(T, 𝒪)`, and similarly for
`e'`. `P : V × V → W` is a morphism.

- `symm_single_eq_comp he T l`. Let `e` be natural (`IsNaturalVectorCoordinates e`: pulling
  a point back along `f : W → T` applies `f` to its coordinates). Then the `T`-point with
  coordinates the basis vector `Pi.single l 1` is the pullback, along the structure morphism
  `T → Spec k`, of the rational point with the same coordinates.

  Proof. Apply `e T` to both sides. By naturality the right side has coordinates
  `f(Pi.single l 1)` with `f` a ring map, which is `Pi.single l 1` again; compare
  coordinatewise.

- `lift_comp_eq_one_of_rationalPoints he hP h T x y`. Let `e` be natural and let `P` be
  bilinear in the coordinates `e`, `e'` (`IsBilinearVectorPairing e e' P`). If `P(x, y) = 1`
  for all rational points `x, y` of `V`, then `P(x, y) = 1` for all `T`-points `x, y`, for
  every test scheme `T`.

  Proof. Over `T`, read `P` in coordinates as a map
  `f : (Fin d → Γ(T, 𝒪)) → (Fin d → Γ(T, 𝒪)) → (Fin m → Γ(T, 𝒪))`. The four clauses of
  `IsBilinearVectorPairing` make `f` additive and `Γ(T, 𝒪)`-linear in each argument, so `f`
  is a bilinear map `B` (`LinearMap.mk₂`). On pairs of standard basis vectors, `B` is the
  pullback of the value of `P` on two rational points (`symm_single_eq_comp`), which is `1`
  by hypothesis; so `B` vanishes on the basis and `B = 0` (`LinearMap.ext_basis`). Evaluating
  `B = 0` at the coordinates of `x` and `y` and applying the injectivity of `e' T` gives
  `P(x, y) = 1`.

## Root groups

In this section `S` is a commutative group scheme over `Spec k` with `i : S → G`, `a` is a
character of `S`, `j : U → G` represents `RelativeRoot.subgroup i a`, and `j₂ : U₂ → G`
represents `RelativeRoot.subgroup i (2 • a)`.

- `DoubleRootCommutatorPairing.commute_of_lift_pairing_eq_one C g h hp`: two `T`-points `g`,
  `h` of `U` commute when the pairing of their images in `C.V` is `1`.

  Proof. The field `C.lift_pairing` says that the pairing, mapped to `G`, is the commutator
  `g h g⁻¹ h⁻¹` of the images of `g` and `h` in `G`. If the pairing is `1`, the images commute,
  and `g`, `h` commute because `j` is a monomorphism.

From here on `G.X → Spec k` is affine and smooth.

- `DoubleRootCommutatorPairing.lift_pairing_eq_one_of_rationalPoints C hS ha hhigh h T x y`.
  Let `S` be a split torus, `a ≠ 0`, and suppose no `n • a` with `n ≥ 3` is a relative root.
  If the commutator pairing is `1` on all pairs of rational points of `C.V`, it is `1` on all
  pairs of `T`-points, for every `T`.

  Proof. `exists_bilinear_coordinates` gives weight vector coordinates (in particular natural
  ones) in which `C.pairing` is bilinear; apply `lift_comp_eq_one_of_rationalPoints`.

Let `N : HeisenbergNormalForm C` be a Heisenberg normal form: a section `N.sec : C.V → U` of
the quotient map and a cocycle `N.cocycle : C.V × C.V → U₂`.

- `HeisenbergNormalForm.lift_pairing_eq_one_of_commute_rationalPoints N h x y`: if any two
  rational points of `U` commute, the commutator pairing is `1` on all pairs of rational points
  `x`, `y` of `C.V`.

  Proof. Apply `C.lift_pairing` to the lifts `x ≫ N.sec` and `y ≫ N.sec`, whose images in
  `C.V` are `x` and `y` (`N.sec_comp`). The lifts are rational points of `U`, so they commute
  and the commutator on the right is `1`; since `j₂` is a monomorphism, the pairing is `1`.

- `HeisenbergNormalForm.commute_of_commute_rationalPoints N hS ha hhigh h :
  PointsCommute U`. Under the hypotheses on `S` and `a` above: if any two rational points of
  `U` commute, then any two `T`-points of `U` commute, for every test scheme `T`.

  Proof. Combine the previous lemma, `lift_pairing_eq_one_of_rationalPoints` and
  `commute_of_lift_pairing_eq_one`.

- `HeisenbergNormalForm.exists_ne_swap_of_not_commute N hS ha hhigh first hfirst second
  hsecond g g' hgg'`. Let `first : E → rationalPoints C.V` be surjective and
  `second : rationalPoints U₂ → F` injective, for arbitrary types `E`, `F`. If two `T`-points
  `g`, `g'` of `U` over some test scheme `T` do not commute, then there are `x, y : E` with
  `second (N.cocycle (first x, first y)) ≠ second (N.cocycle (first y, first x))`.

  Proof. Otherwise injectivity of `second` makes the cocycle symmetric on rational points. By
  `HeisenbergNormalForm.pairing_eq`, the pairing is the cocycle times the inverse of the swapped
  cocycle, so (by surjectivity of `first`) the pairing is `1` on all rational points. Then
  `lift_pairing_eq_one_of_rationalPoints` and `commute_of_lift_pairing_eq_one` show that `g`
  and `g'` commute, which is a contradiction.

- `HeisenbergNormalForm.exists_form_ne_swap N hS ha hhigh first second form cocycle_eq g g'
  hgg'`. Let `E` be an additive group and `W` an additive subgroup of `E`. Let
  `first : Multiplicative E ≃* rationalPoints C.V` and
  `second : Multiplicative W ≃* rationalPoints U₂` be coordinates, and let `form : E → E → E`
  satisfy `cocycle_eq`: the coordinate under `second` of the cocycle at
  `(first x, first y)` is `form x y`. If two `T`-points of `U` over some test scheme do not
  commute, then `form x y ≠ form y x` for some `x, y : E`.

  Proof. Apply `exists_ne_swap_of_not_commute` with `first` read on `E` (surjective because
  `first` is an equivalence) and `second` the coordinate of `second.symm` in `E` (injective
  because `second.symm` is injective and `W → E` is injective), then rewrite by `cocycle_eq`.

  In `HeisenbergUnitaryData`, `E` is the quadratic extension and `W` its trace-zero subgroup.
