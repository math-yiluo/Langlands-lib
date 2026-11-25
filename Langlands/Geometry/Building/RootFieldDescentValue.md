# Values of the actual apartment on actual root-field points

Lean module: `Langlands.Geometry.Building.RootFieldDescentValue`.

This is internal infrastructure on the way to KP Lemma C.5.3. It
computes the values of every point of the actual apartment class of a maximal
split torus on the actual root-field points of a relative root with no higher
multiples. As a consequence, the filtration subgroups `U_{a,y,r}` of
Kaletha–Prasad (*Bruhat–Tits Theory: A New Approach*, 2023, Definition 6.1.2,
axiom V 1) are shifted additive filtrations of the published root-field
coordinates. The content is derived from published Library results:

- the split value formula on actual root lines
  (`exists_rootLine_value_of_isSplitTorus`, module `SplitRootLineValue`);
- the Galois comparison of fibre coordinates
  (`fiber_coordinate_value_eq_of_galois`,
  `torusRestrictedRootFunctionFamily_eq_of_coordinates`);
- the actual root-field point product
  (`rootOrbitFieldPoint_fieldExtend_eq_product`);
- the descent of a Galois-fixed split apartment point, as assembled in
  `exists_isOmegaCompatible_of_descent` (module `QuasiSplitApartmentAssembly`),
  with V 5 at multipliable roots supplied by `quasiSplitMultipliableOpposite`;
- uniqueness of integer apartment classes satisfying V 6
  (`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus_of_centralizers`).

The statement that root-group valuations along root-field coordinates are the
field valuation plus a constant is standard. Its formulation here, through the
Library's actual root-field points and coordinates, is internal. The module makes
no further claim from the literature.

## Setting

Work at arbitrary universe `u`. `k` is a field and `L/k` a finite Galois
extension. `G` is a smooth affine group scheme of locally finite type over
`Spec k`, with `f : S ⟶ T` and `j : T ⟶ G`. The notation `G_L`, `T_L`, `S_L`,
`j_L`, `f_L` denotes base change along `Spec L → Spec k`, and `a_L` the base
change of a character `a` of `S`. `v` is a `ℤ`-valued valuation of `k` that is
surjective onto `WithZero (Multiplicative ℤ)`, with henselian valuation ring.
For a finite separable extension `E/k`, `ω_E` is
`FieldTheory.henselianSeparableAddValuation v hH E`, the normalized unique
extension of `v` to `E`.

`a` is a relative root of `f ≫ j` such that no multiple `n • a` with `n ≥ 2` is
a relative root (`RelativeRoot.HasNoHigherRoots`). `β` is an absolute root of
`j_L` whose Galois orbit is the whole restriction fibre of `a`. `L_a` is the
root field `rootOrbitField k L j β`. For `x ∈ L_a`, `rootOrbitFieldPoint … x` is
the actual rational root-group point with root-field coordinate `x`.

The private instances `rootFieldDescentAffine` and `rootFieldDescentSmooth`
record that `G_L` is affine and smooth over `Spec L`. They unfold the base
change to the pullback. `rootFieldDescentSeparable` records that `L_a` is
separable over `k`, as a subextension of the Galois extension `L`.

## Restricted values of a Galois-fixed split point

`exists_torusFieldRestricted_value_rootOrbitFieldPoint`. Assume `G` is connected
reductive, `j` is a maximal torus, `S` is split, `T_L` is split, `G_L` is
connected reductive, `j_L` is a maximal torus with the opposite-factor-pair
property, and `j_L` is a monomorphism. Let `DK` be any normalizer-stable
apartment class of `j_L` for the real order of the normalized henselian
valuation of `L`. Let `xK` be a point of `DK` fixed by the Galois action on
root-function families. Then there is a real `c` such that for every nonzero
`x ∈ L_a`,

`torusFieldRestrictedRootFunctionFamily … xK.isValuation f_L a (rootOrbitFieldPoint … x) = ω_{L_a}(x) + c`.

Proof. Enumerate the orbit of `β` by `Fin n`, giving the injective family `A` of
absolute roots. Its range is exactly the set of roots of `j_L` restricting to
`a_L`, and any two members are Galois conjugate. Apply the split value formula
of `SplitRootLineValue` at the first root `A l₀`, along the root line given by
the published root-orbit line equivalence. This yields a constant `c`. The
actual root-field point, extended to `L`, is the product of the points
`X l` whose root-line coordinates are the conjugate embeddings of `x`
(`rootOrbitFieldPoint_fieldExtend_eq_product`). The Galois comparison of fibre
coordinates gives the value of `xK` at every `X l` equal to its value at
`X l₀`. That value is `ω_L(e(x)) + c` for the embedding `e`. This equals
`ω_{L_a}(x) + c` by uniqueness of the extended valuation
(`henselianSeparableAddValuation_algHom`). Since `x ≠ 0` the value is a real
number `t + c`. The coordinate theorem
`torusRestrictedRootFunctionFamily_eq_of_coordinates` then gives the torus
restriction at the product, and unfolding the field restriction finishes.

## Values of the actual apartment

`exists_apartment_value_rootOrbitFieldPoint`. Assume in addition that `T` is
affine and of locally finite type, that `i : S ⟶ G` is a monomorphic maximal
split torus with `f ≫ j = i`, that `j` is a closed subgroup representing the
full centralizer of `i`, and that `j_L` is a maximal torus. Let
`D : KPApartmentData i (IntegerValuation.order v)` satisfy V 6
(`IntegerValuation.IsOmegaCompatible v D C`) for some centralizer datum `C` of
`i`. Then for every point `y` of `D` there is a real `c` such that for every
`x ∈ L_a`, including `x = 0`,

`y.val a (rootOrbitFieldPoint … x) = ω_{L_a}(x) + c`.

Proof. The body repeats the construction in
`exists_isOmegaCompatible_of_descent` with the field `L`, the torus `T` and the
maps `f`, `j`. It forms the split apartment class `DK` of `j_L` for the
normalized henselian valuation of `L` and its Galois-fixed point `xK`. It
proves the original-point shifts and axiom V 5. At multipliable roots V 5 is
`quasiSplitMultipliableOpposite`; otherwise it is
`torusFieldRestrictedRootFunctionFamily_opposite_of_two_not_mem`. This gives the
descended valuation `ψ` and the apartment class `D'`, the orbit of `ψ` under
`V(S)`. With the centralizer datum `(T, j, f)`, whose bijectivity is
`Cartan.restrictionEvaluation_bijective_of_torusCentralizer`, the class `D'`
satisfies V 6. Uniqueness of V 6 classes gives `D = D'`. So `y.val = w +ᵥ ψ`
for some `w ∈ V(S)`, and `y.val a g = ψ a g + a(w)`. Here `ψ` is the
torus-then-field restriction of `xK`. The previous theorem then gives the
formula with constant `c₁ + a(w)` for `x ≠ 0`. For `x = 0` the actual
root-field point is `1`, since both equivalences defining it are additive. So
the left side is `⊤` by the valuation axiom `eq_top_iff`, and the right side is
`⊤ + c = ⊤`.

## Filtrations

`exists_filtration_eq_additiveRootFiltration`. Take `i = f ≫ j` in the previous
theorem, with `T` and `S` affine and `β` in the restriction fibre of `a`. Let
`e` be the coordinate equivalence of the published root-field coordinates
`rootFieldCoordinatesOfOrbit … β hβ horbit`. Then there is a real `c` such that
for every depth `r`,

`D.filtration y a r = additiveRootFiltration ω_{L_a} e (r - c)`.

Proof. Take `c` from the previous theorem. A point `g` of the root group equals
`e (ofAdd x)` with `x = (e.symm g).toAdd`, and `e (ofAdd x)` is definitionally
the actual root-field point of `x`. Hence `y.val a g = additiveRootValue ω e g + c`.
For `t ∈ WithTop ℝ`, `r ≤ t + c` holds exactly when `r - c ≤ t`; the case
`t = ⊤` is trivial and the real case is linear arithmetic. Both subgroups
consist of root-group points, so membership agrees.

`rootFieldDepthShift` (definition). With the hypotheses of the previous theorem,
`rootFieldDepthShift … y : ℝ` is the constant chosen by
`exists_filtration_eq_additiveRootFiltration`.

`filtration_eq_additiveRootFiltration_rootFieldDepthShift`. For every depth `r`,
`D.filtration y a r` is
`additiveRootFiltration ω_{L_a} e (r - rootFieldDepthShift … y)`. This is the
choice specification.

## Scope

All results concern relative roots `a` with no higher multiples. Roots `a` for
which some `n • a` with `n ≥ 2` is a relative root, in particular multipliable
roots with `2a` a root, are not covered here. (Inside the proof of
`exists_apartment_value_rootOrbitFieldPoint`, V 5 at multipliable roots is
needed only to construct the descended class `D'`.) The results use only
standard axioms.
