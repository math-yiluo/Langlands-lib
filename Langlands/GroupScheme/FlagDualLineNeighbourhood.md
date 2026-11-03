# Invariant affine neighbourhoods from semi-invariant dual lines

Author: Worker 967.

This internal module provides glue for the invariant-affine-neighbourhood step of
the flag argument (task `877d0194-f7d3-4c1e-8e72-e81d1a772c0c`). It combines the
chart lemma of `Langlands.GroupScheme.ProjectiveDualLineChart` with the projective
embedding of `Langlands.GroupScheme.ProjectiveQuotientEmbedding`. The result is
`exists_invariantAffineOpen_of_dualLines`. Let `q : G → Q` be a quotient of a
smooth affine group by a smooth closed subgroup `B`, with `Q` proper. Assume `B`
is the stabilizer of a coordinate line of a representation `ρ`. Assume that for
each rational point `g` of `G` there is a linear form `w` that does not vanish
on `ρ(g) e_j` and whose line is stable under the rational points of a smooth
subgroup `U`. Then every rational point of `Q` has a `U`-invariant affine open
neighbourhood. The hypothesis on linear forms is the conclusion of the Library
statement `FlagCoreDualLineStatement`, which is not proved here.

Mathematically this is the step of the proof of Milne, *Algebraic Groups*
(2017), Theorem 17.65, where the `U`-stable affine open `D₊(w)` of `P(V)` is
intersected with the closed subvariety `G/B`. Two points are not in Milne and
are added here:

- Milne's semi-invariance of `w` is on points. The chart lemma needs it on all
  tests. Since `U` is smooth, hence reduced, the rational-point statement
  implies the all-test statement (`exists_unit_vecMul_of_rationalPoints`).
- The chart lemma uses a translated coordinate chart. The linear form `w` is
  turned into a basis change with `w` as one row (`dualLineChange`).

The module uses no structure theory of algebraic groups. In particular it does
not prove that `Q` is proper, and it does not produce the linear forms; both are
explicit hypotheses of the last theorem. Every declaration is derived from
existing Library and Mathlib APIs. No new external result is used.

## Charts at translated basis points

- `ProjectiveSpace.CoordinateLines.basisPoint_linearAction_preimage_coordinateOpen`
  (namespace `Langlands.AlgebraicGeometry`): `R` is a commutative ring, `X` a
  scheme with an `R`-algebra structure on `Γ(X, ⊤)`, and `e` a linear
  automorphism of `R^{n+1}`. Take the `X`-point of `Pⁿ_R` given by the basis
  vector `e_j` (the Library's `basisPoint`), followed by the projective linear
  action of `e`. The inverse image of the chart `D₊(X_{j₀})` under this composite
  is the basic open of `X` of the image of `(e e_j)_{j₀}` in `Γ(X, ⊤)`. The proof
  writes the composite as the point `Proj.fromOfGlobalSections` of the composite
  ring map (`fromOfGlobalSections_comp_gradedMap`). It then applies Mathlib's
  `Proj.fromOfGlobalSections_preimage_basicOpen` to `X_{j₀}`, whose image under
  the substituted evaluation is `(e e_j)_{j₀}`.
- `RelativeProjectiveSpace.basisSection_globalLinearAction_preimage_coordinateOpen`:
  the relative version. For a linear automorphism `e` of `Γ(X, ⊤)^{n+1}`, the
  basis section `e_j` of `Pⁿ_X` followed by the global linear action of `e` pulls
  the relative chart `D₊(X_{j₀})` back to the basic open of `(e e_j)_{j₀}`. The
  proof uses `toPolynomial_preimage_coordinateOpen` from
  `ProjectiveDualLineChart` to reduce to the previous lemma over `R = Γ(X, ⊤)`.
- `ProjectiveOrbit.basisSection_matrixAction_preimage_coordinateOpen`: for
  `N ∈ GL_{n+1}(Γ(T, ⊤))`, the basis section `e_j` of `Pⁿ_T` followed by
  `matrixAction n N` pulls `D₊(X_{j₀})` back to the basic open of the entry
  `N_{j₀ j}`.
- `ProjectiveOrbit.comp_orbitMap_basisSection_preimage_translatedChart`: let `ρ`
  be a matrix representation of a group `G` over `Spec R`, `g : Z → G` a test
  point and `P ∈ GL_{n+1}(Γ(Spec R, ⊤))`. Take the test point `g` of `G`,
  followed by the orbit map of the basis section `e_j`, that is
  `g ↦ [ρ(g) e_j]`. Its underlying map pulls the translated chart
  `translatedChart P j₀` back to the basic open of `Z.left` of the `(j₀, j)`
  entry of `P_Z ρ(g)`. Here `P_Z` is the image of `P` under `Z.hom.appTop`. The
  proof uses the Library's `comp_orbitMap`, `pullbackPoint_basisSection` and
  `matrixAction_mul`, the base-change lemma `map_preimage_translatedChart`, and
  the previous lemma.

## Rational points of reduced schemes

From here on `k` is a field and schemes are over `Spec k`. A rational point of
`Z` is a morphism `Over.mk (𝟙 (Spec k)) ⟶ Z`.

- `eq_of_rationalPoints`: let `k` be algebraically closed and let `Z` be reduced
  and locally of finite type over `k`. Two global functions `f, g` of `Z` with
  equal pullbacks along every rational point are equal. Suppose not. Since `Z`
  is reduced, the basic open `D(f - g)` is nonempty (Mathlib's
  `basicOpen_eq_bot_iff`). `Z` is a Jacobson space, so `D(f - g)` contains a
  closed point. Over an algebraically closed field a closed point is a rational
  point (Mathlib's `pointOfClosedPoint`). At this point `f - g` is invertible,
  but `f` and `g` have equal pullbacks; contradiction.
- `rationalEval z : Γ(Z, ⊤) →+* k` is evaluation at the rational point `z`, that
  is pullback along `z` followed by `Γ(Spec k, ⊤) ≅ k`.
- `rationalEval_scalarMap`: `rationalEval z` sends the image `scalarMap Z c` of a
  scalar `c ∈ k` to `c`.
- `eq_of_rationalEval`: under the hypotheses of `eq_of_rationalPoints`, two
  global functions with equal values `rationalEval z` at every rational point
  are equal.
- `map_rationalEval_pointMatrix`: for a matrix representation `σ` of a group `H`
  and a rational point `z` of `H`, applying `rationalEval z` entrywise to the
  universal matrix `σ.pointMatrix H (𝟙 H)` gives the Library's rational matrix
  `σ.rationalMatrix z`.

## Semi-invariance on all tests

- `exists_unit_vecMul_of_rationalPoints`: let `k` be algebraically closed and
  let `H` be a group scheme over `k` that is reduced and locally of finite type.
  Let `σ` be a matrix representation of `H` and `w ∈ k^m` a row vector with
  `w_{j₀} ≠ 0`. Assume that for every rational point `x` there is `c ∈ kˣ` with
  `w σ(x) = c w`. Then for every test `Z` and every `h : Z → H` there is a unit
  `c` of `Γ(Z, ⊤)` with `w σ(h) = c w`, where `w` is mapped to `Γ(Z, ⊤)` by
  `scalarMap`. The proof works with the universal matrix `g₀ = σ(𝟙 H)` over
  `A = Γ(H, ⊤)` and writes `W` for `w` viewed in `A`. The assumption, and the
  same assumption for inverse matrices (with `c⁻¹`), give at every rational
  point the identities `(W g₀)_l W_{j₀} = (W g₀)_{j₀} W_l` and the same for
  `g₀⁻¹`. By `eq_of_rationalEval` these identities hold in `A`. Since `W_{j₀}`
  is a unit, `W g₀ = c₀ W` and `W g₀⁻¹ = d₀ W` with
  `c₀ = (W g₀)_{j₀} W_{j₀}⁻¹` and `d₀` analogous. From `g₀ g₀⁻¹ = 1` follows
  `c₀ d₀ = 1`, so `c₀` is a unit. Pulling back along `h` and using naturality of
  `σ.pointMatrix` gives the claim.

## The basis change of a linear form

- `det_one_updateRow`: replacing row `j₀` of the identity matrix by `w` gives a
  matrix with determinant `w_{j₀}`.
- `dualLineChange w j₀ hw`, for `w ∈ k^{n+1}` with `w_{j₀} ≠ 0`, is that matrix,
  as an element of `GL_{n+1}(Γ(Spec k, ⊤))`. It is invertible by
  `det_one_updateRow`. Informally, `translatedChart (dualLineChange w j₀ hw) j₀`
  is the open `D₊(w)` of the ambient projective space; this is not stated in
  Lean.
- `dualLineChange_row`: on every test `Z`, row `j₀` of the image of
  `dualLineChange w j₀ hw` in `GL_{n+1}(Γ(Z, ⊤))` is `w`, mapped by
  `scalarMap`.
- `dualLineChange_mul_apply`: for `M ∈ GL_{n+1}(Γ(Z, ⊤))`, the `(j₀, l)` entry
  of `P_Z M` is the `l`-th entry of `w M`, where `P = dualLineChange w j₀ hw`.
- `rationalEval_id`: evaluation at the identity rational point of
  `Over.mk (𝟙 (Spec k))` is the canonical identification `Γ(Spec k, ⊤) ≅ k`.

## Local assembly

`exists_invariantAffineOpen_of_dualLines` has the following hypotheses. The
field `k` is algebraically closed.

- `G` is a smooth affine group scheme over `k`. It need not be connected.
- `b : B → G` is a closed subgroup with `B` smooth (`hb`, `hB`).
- `i : U → G` is a homomorphism with `U` smooth (`hU`).
- `ρ` is a representation of `G` on `k^{n+1}` and `j` an index. `hρ` says that,
  on every test, a point of `G` lies in the range of `b` iff it maps `e_j` to a
  unit multiple of `e_j`.
- `Q` is proper over `k` (`IsProper Q.hom`). The map `q : G → Q` is flat,
  surjective and quasi-compact. `hfib` says that its fibres on every test are the
  cosets of `B`.
- `a` is an action of `G` on `Q` with `a.act g (h ≫ q) = (g * h) ≫ q` (`hact`).
- `hw`: for every rational point `g` of `G` there is `w ∈ k^{n+1}` with
  `w · ρ(g) e_j ≠ 0` and, for every rational point `x` of `U`, `w ρ(x) = c w`
  for some `c ∈ kˣ`.

The conclusion: for every rational point `x` of `Q` there is an affine open `V`
of `Q` that contains the image of `x`. It also satisfies
`(a.restrict i).hom.left ⁻¹ᵁ V = (snd U.X Q).left ⁻¹ᵁ V`, the invariance
condition of `FlagInvariantAffineOpenCoverStatement`.

Proof. The map `q` is locally of finite type, since its composite with
`Q → Spec k` is the structure map of the smooth `G`. Since `q` is also
surjective, `x` lifts to a rational point `g` of `G` (Library
`exists_point_lift_of_locallyOfFiniteType_surjective`). Take `w` from `hw g`.
Some coordinate `w_{j₀}` is nonzero, since `w · ρ(g) e_j ≠ 0`. Let `φ` be the
descended orbit map `quotientOrbitMap` of `ProjectiveQuotientEmbedding`. It is a
closed immersion by `isClosedImmersion_quotientOrbitMap`, and matrix equivariant
by `isMatrixEquivariant_quotientOrbitMap`. `U` is reduced, being smooth over a
field (Library `isReduced_of_smooth_over_field`). By
`exists_unit_vecMul_of_rationalPoints` for the restricted representation
`ρ.restrict i`, row `j₀` of `P = dualLineChange w j₀ hw` is semi-invariant on
all tests (`dualLineChange_row`). Then
`isAffineOpen_isInvariantOpen_preimage_translatedChart` shows that
`V = φ⁻¹(translatedChart P j₀)` is affine and invariant. Finally, `x = g ≫ q`
and `q ≫ φ` is the orbit map. By
`comp_orbitMap_basisSection_preimage_translatedChart` and
`dualLineChange_mul_apply`, `x` pulls `V` back to the basic open of
`(w ρ(g))_j`. Its value under `rationalEval_id` is `w · ρ(g) e_j ≠ 0`, so it is
a unit, and the basic open is all of `Spec k`.
