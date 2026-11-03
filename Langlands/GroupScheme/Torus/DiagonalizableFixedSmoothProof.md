# Smooth fixed subgroups for diagonalizable actions: proof

`Langlands.GroupScheme.Diagonalizable.FixedSmooth.fixedSubgroupSmooth` proves
`Langlands.GroupScheme.Diagonalizable.FixedSubgroupSmoothStatement.{u}` for every
universe `u`. This is the smoothness part of Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), Proposition A.8.10(2), printed
pp. 547–550 (PDF pp. 573–576). As in that source, the proof uses the
infinitesimal lifting criterion. The linear reductivity of `D(Λ)` enters as the
exact degree-zero projection of the `Λ`-grading on coordinates. The Lean route
below works directly with the coaction on the chosen coordinate algebra. It needs
no quotient of that algebra by the ideal of the fixed locus.

## Degree-zero lifts

The section `Algebra` works with `R`-algebras `A` and `B`, an additive commutative
group `Λ`, and an `R`-algebra map `ρ : A → A[Λ]`.

* `map_coeff_zero_mul`: let `ψ : A → B` be an `R`-algebra map and `J ⊆ B` an
  ideal with `J ^ 2 = ⊥`. Suppose `x, y ∈ A[Λ]` have every nonzero-degree
  coefficient mapped into `J` by `ψ`. Then `ψ ((x y)₀) = ψ (x₀) ψ (y₀)`. In the
  convolution formula for `(x y)₀`, every term other than `x₀ y₀` is a product
  of two elements of `J`, hence zero.
* `degreeZeroLift ρ ψ hJ hψ` is the map `a ↦ ψ ((ρ a)₀)`. It assumes that `ψ`
  sends each nonzero-degree coefficient of each `ρ a` into `J`. The previous
  lemma makes it multiplicative, so it is an `R`-algebra map.
  `degreeZeroLift_apply` is its defining equation.
* `map_eq_map_coeff_zero`: assume the counit law
  `∑_γ (ρ a)_γ = a`. Then any `R`-algebra map `f` that kills every
  nonzero-degree coefficient of every `ρ a` satisfies `f a = f ((ρ a)₀)`.

## Monomial evaluations

The section `Monomial` collects facts about Mathlib's `liftNCAlgHom` on group
algebras, which evaluates `A[Λ]` given a map on `A` and a character on `Λ`.
`liftNC_apply` writes the evaluation as a finite sum over coefficients.
`liftNCAlgHom_singleZero` identifies evaluation at the monomials after a base
map `f` with `mapAlgHom Λ f`. `liftNCAlgHom_apply_of_coeff` says that evaluation
at any character only sees the degree-zero coefficient when `f` kills the others.
`liftNCAlgHom_singleZero_singleZero` identifies one evaluation into `A[Λ][Λ]`
with the outer degree-zero inclusion. `coeff_liftNCAlgHom_diag` uses a character
sending `γ` to the monomial `X^γ Y^γ` in `A[Λ][Λ]`. Evaluation at it sends
`y ∈ A[Λ]` to an element whose outer degree-`n` coefficient is the inner monomial
`y_n X^n`.

## The coaction

The section `Geometry` has a base `R : CommRingCat`, an additive commutative group
`Λ`, a group scheme `G` over `Spec R` with affine structure map, and an
automorphic action `a` of `D(Λ) = Diagonalizable.groupScheme R Λ` on `G`. The
coordinate algebra `A = Lie.coordinateAlgebra G` and the bijection
`Lie.pointCoordinates G` between affine points over `Spec B` and `R`-algebra maps
`A → B` are the published affine presentation.

* `charEquiv B` is the existing corepresentation of `D(Λ)` by the group algebra.
  It identifies points of `D(Λ)` over `Spec B` with characters
  `Multiplicative Λ →* Bˣ`, and `charPt B χ` is the point of a character `χ`.
  `charEquiv_map`, `charEquiv_naturality`, `charPt_eq`, `charPt_mul`,
  `charPt_one` and `map_comp_charPt` record its compatibility with the
  corepresentation, with base change and with the group law.
* `coaction a : A → A[Λ]` is the coordinate map of the point obtained by acting
  with the universal character `γ ↦ X^γ` on the tautological point of `G` over
  `Spec A[Λ]`.
* `pointCoordinates_act`: for a character `χ` and an affine point `g` over
  `Spec B`, the point `χ · g` has coordinates `evalχ ∘ (coordinates of g) ∘ ρ`.
  Here `evalχ` sends `X^γ` to `χ γ`. Both sides are base changes of the universal
  case along one algebra map, and the action is natural in the test scheme.
* `coaction_counit` is the counit law `∑_γ (ρ x)_γ = x`. It is the previous
  formula for the trivial character on the tautological point, using
  `act_one_left`.
* `coaction_coeff` is homogeneity: `ρ ((ρ x)_n) = X^n (ρ x)_n`. It compares both
  sides of `act_mul_left` for two characters with values in `A[Λ][Λ]`, acting on
  the tautological point placed in degree zero. The characters are the outer
  monomials `Y^γ` and the inner monomials `X^γ` placed in outer degree zero. Their
  product is the character `X^γ Y^γ` of `coeff_liftNCAlgHom_diag`. Reading off
  outer coefficients yields the identity.
* `pointCoordinates_coeff_eq_zero`: if `g` over `Spec B` is fixed, then its
  coordinates kill every nonzero-degree coefficient of every `ρ x`. Apply
  fixedness to the refinement `Spec B[Λ] → Spec B` and the universal character
  over `B[Λ]`. Then applying the coordinates of `g` coefficientwise to `ρ x`
  gives an element of degree zero.
* `isFixed_of_coeff` is the converse, for fixedness on every refinement: suppose
  the coordinates of `g` over `Spec B` kill all such coefficients. Let
  `b : T' → Spec B` be a refinement and `h : T' → D(Λ)` a point. Through the unit
  of the `Γ ⊣ Spec` adjunction, both factor through `Spec Γ(T')` as a base map `e`
  and a character `χ` over `Γ(T')`. By `liftNCAlgHom_apply_of_coeff` and
  `map_eq_map_coeff_zero`, the character `χ` fixes the base change of `g` along
  `e`, and naturality of the action gives `h · (g ∘ b) = g ∘ b`.

## Formal smoothness of the fixed subgroup

`formallySmooth_of_isRepresentedBy` works over an arbitrary base `R`. Let `C` be
a group scheme with affine structure map and `j : C ⟶ G` represent
`a.fixedSubgroup`. Assume that `A` is formally smooth over `R`. Then
`Lie.coordinateAlgebra C` is formally smooth over `R`. The proof uses
`Algebra.FormallySmooth.of_comp_surjective`, so a square-zero ideal `I` of an
`R`-algebra `B` and an `R`-algebra map `f` from the coordinates of `C` to `B/I`
are given.

1. Let `x0` be the point of `C` over `Spec (B/I)` with coordinates `f`. Its image
   `x0 ≫ j` lies in the range of `j`, so it is fixed. Let `g0` be its
   coordinates. By `pointCoordinates_coeff_eq_zero`, `g0` kills the
   nonzero-degree coaction coefficients.
2. Formal smoothness of `A` gives a lift `ψ : A → B` of `g0`. Then `ψ` sends the
   nonzero-degree coaction coefficients into `I`. Hence
   `ψ' = degreeZeroLift (coaction a) ψ` is an algebra map.
3. Homogeneity (`coaction_coeff`) shows that `ψ'` kills every nonzero-degree
   coefficient, and the counit law shows that `ψ'` still lifts `g0`.
4. By `isFixed_of_coeff`, the point with coordinates `ψ'` is fixed. Since `j`
   represents the fixed subgroup, it equals `x ≫ j` for a point `x` of `C` over
   `Spec B`. Since `j` is a monomorphism, the reduction of `x` modulo `I` is
   `x0`. So the coordinates of `x` lift `f`.

## The exact statement

`fixedSubgroupSmooth` introduces the data of `FixedSubgroupSmoothStatement`: a
field `k`, a finitely generated `Λ`, a smooth affine `G`, an action `a`, and a
representative `j : C ⟶ G` with `IsClosedSubgroup j`. The closed immersion is
affine. Thus `C` has affine structure map, since by `Over.w` it is the composite
of `j` with the structure map of `G`. Worker 1345's
`FixedSubgroupSmoothAlgebraBridge.coordinateAlgebra_smooth` makes the coordinate
algebra of `G` smooth, hence formally smooth, over `k`. The previous section makes
the coordinate algebra of `C` formally smooth. Then
`FixedSubgroupSmoothAlgebraBridge.smooth_of_formallySmooth` concludes
`Smooth C.X.hom`.

The proof does not use finite generation of `Λ` or the group structure of `G`
beyond the action and the representing morphism. It places no condition on
torsion in `Λ`, on the characteristic of `k`, or on reducedness of `D(Λ)`.
Fixedness is the all-refinement `AutomorphicAction.fixedSubgroup` of the
statement. The closed representative remains a premise, as in the statement.
