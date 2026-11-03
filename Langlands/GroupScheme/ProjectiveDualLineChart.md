# Invariant coordinate charts of matrix-equivariant maps to projective space

Author: Worker 967.

This internal module provides glue for the invariant-affine-neighbourhood step of
the flag argument (task `877d0194-f7d3-4c1e-8e72-e81d1a772c0c`). Suppose a group
scheme acts on `X` and a map `φ : X → Pⁿ` intertwines that action with a matrix
representation. Suppose also that a subgroup fixes a linear form up to units.
Then the inverse image under `φ` of the corresponding chart is an open subscheme
invariant under that subgroup. If moreover `φ` is an affine morphism (for
example a closed immersion), this inverse image is also affine. Without that
assumption it need not be: the constant map `P¹ → P¹` with value `[1 : 0]` is
equivariant for the trivial group and representation, and the inverse image of
`D₊(X_0)` is all of `P¹`. Mathematically this is the step "`D₊(w)` is a
`U`-stable affine open of `Pⁿ`, so its trace on the closed subvariety `G/B` is a
`U`-stable affine open" in the proof of Milne, *Algebraic Groups* (2017),
Theorem 17.65. It uses no structure theory of algebraic groups. Every declaration below is derived from the existing projective-space,
projective-orbit, matrix-representation and invariant-open APIs of the Library.
No new external result is used. The module does not construct `φ`, the
representation, or the linear form.

## Charts of projective space

In namespace `Langlands.AlgebraicGeometry`:

- `ProjectiveSpace.linearAction_preimage_coordinateOpen` works over a commutative
  ring `R`. Let `e` be a linear automorphism of `R^{n+1}` and `c` a unit of `R`
  with `proj_j ∘ e = c • proj_j`, that is, the `j`-th coordinate of `e v` is
  `c * v_j`. Then the projective linear action of `e` on `Pⁿ_R` pulls the
  coordinate chart `D₊(X_j)` back to itself. The proof uses the Library's
  description of points of the inverse image by the linear substitution of `X_j`;
  that substitution is `c X_j`, a unit multiple of `X_j`.
The relative chart `D₊(X_j)` of `Pⁿ_S` is the Library's
`RelativeProjectiveSpace.coordinateOpen S n j`, the inverse image of the chart
`D₊(X_j)` of integral projective space `Pⁿ_ℤ` under the integral projection
`toIntegral`. This module uses the Library's facts that base change preserves it
(`RelativeProjectiveSpace.map_preimage_coordinateOpen`) and that it is affine
over an affine base (`RelativeProjectiveSpace.isAffineOpen_coordinateOpen`). It
adds:

- `RelativeProjectiveSpace.toPolynomial_preimage_coordinateOpen`: for every map
  `a : S → Spec K`, the polynomial projection `Pⁿ_S → Pⁿ_K` determined by `a`
  pulls `D₊(X_j)` of `Pⁿ_K` back to the relative chart.
- `RelativeProjectiveSpace.linearAction_preimage_coordinateOpen` is the relative
  version of the first lemma, for a coefficient linear automorphism given over
  `K` through `a : S → Spec K`.

## Matrix actions and translated charts

In namespace `Langlands.GroupScheme.ProjectiveOrbit`, with `matrixAction n M`
the Library's action of `M ∈ GL_{n+1}(Γ(T, ⊤))` on `Pⁿ_T`:

- `matrixAction_preimage_coordinateOpen`: if row `j` of `M` is `c • e_j` for a
  unit `c`, then `matrixAction n M` pulls the chart `D₊(X_j)` of `Pⁿ_T` back to
  itself.
- `matrixAction_preimage_translatedChart`: let `P, M ∈ GL_{n+1}(Γ(T, ⊤))` and
  let `c` be a unit with `(row j of P) · M = c • (row j of P)`, a row vector
  times a matrix (`Matrix.vecMul`). Then `matrixAction n M` pulls the open
  `(matrixAction n P)⁻¹ D₊(X_j)` back to itself. The proof computes that row `j`
  of `P M P⁻¹` is `c • e_j`. It then writes `P M = (P M P⁻¹) P` and uses the
  composition law `matrixAction n (A * B) = matrixAction n B ≫ matrixAction n A`.
- `pointSection y` is defined for a test point `y : Z → ambient n R` of the
  ambient projective scheme over `Spec R`. It is the section
  `Z.left → Pⁿ_{Z.left}` determined by the identity of `Z.left` and by
  `y.left` followed by the integral projection.
- `pointSection_map`: composing `pointSection y` with the base-change map
  `Pⁿ_{Z.left} → Pⁿ_{Spec R}` recovers `y.left`.
- `IsMatrixEquivariant a ρ φ` relates an action `a` of `H` on `X`, a matrix
  representation `ρ` of `H` of size `n + 1` and a map `φ : X → ambient n R`. It
  states that for every test `Z` and every `h : Z → H`, `x : Z → X`, the
  underlying scheme map of `a.act h x ≫ φ` equals the composite
  `pointSection (x ≫ φ)`, then `matrixAction n (ρ.pointMatrix Z h)`, then the
  base-change map to `Pⁿ_{Spec R}`. In words, `φ(h · x) = ρ(h) φ(x)` on all
  tests.
- `IsMatrixEquivariant.restrict`: equivariance for `G` gives equivariance for
  the restricted action `a.restrict f` and the restricted representation
  `ρ.restrict f` along any homomorphism `f : H → G`.
- `translatedChart P j`, for `P ∈ GL_{n+1}(Γ(Spec R, ⊤))`, is the open
  `(matrixAction n P)⁻¹ D₊(X_j)` of the ambient scheme. Informally it is
  `D₊(w)` for the linear form `w = Σ_l P_{jl} X_l` given by row `j` of `P`.
  When `R` is a field, every nonzero linear form is row `j` of some invertible
  `P`. The Lean definition is the inverse image itself; this module proves no
  description of it as `D₊(w)`.
- `isAffineOpen_translatedChart`: the translated chart is affine, because
  `matrixAction n P` is an isomorphism with inverse `matrixAction n P⁻¹`.
- `map_preimage_translatedChart`: base change along `f : Z → Spec R` pulls
  `translatedChart P j` back to the chart of `Pⁿ_Z` translated by the image
  `GL.map f P` of `P`.

## Invariance

- `isInvariantOpen_preimage_translatedChart` takes `a`, `ρ` and `φ` with
  `IsMatrixEquivariant a ρ φ`, and `P`, `j`. Its hypothesis is that, for every
  test `Z` and every `h : Z → H`, some unit `c` of `Γ(Z.left, ⊤)` satisfies
  `(row j of P_Z) · ρ.pointMatrix Z h = c • (row j of P_Z)`, where `P_Z` is the
  image of `P` in `GL_{n+1}(Γ(Z.left, ⊤))`. In words, every point of `H` fixes
  the line of `w` under the dual action. The conclusion is
  `a.IsInvariantOpen (φ.left⁻¹ translatedChart P j)`: the inverse images of this
  open under the action morphism `H × X → X` and under the second projection
  agree. The proof applies equivariance to the universal test
  `Z = H × X`, `h = fst`, `x = snd`, where `a.act fst snd` is the action
  morphism. It then pulls the chart back along the section and uses the
  translated-chart lemma.
- `isAffineOpen_isInvariantOpen_preimage_translatedChart` is the form used by
  the flag step. It takes an action `a` of `G` on `X`, a representation `ρ` of
  `G`, an equivariant `φ` whose underlying scheme map is affine
  (`IsAffineHom φ.left`), and a homomorphism `f : H → G`. Suppose the row
  hypothesis above holds for the points `h ≫ f` of `G` coming from `H`. Then
  `φ.left⁻¹ translatedChart P j` is an affine open. Moreover, its inverse images
  under `(a.restrict f).hom.left` and under the second projection
  `(snd H.X X).left` are equal, which is the invariance equality of
  `FlagInvariantAffineOpenCoverStatement`. Affineness holds because inverse
  images of affine opens under affine morphisms are affine. Invariance is the
  previous lemma for the restricted action and representation.

The row hypothesis is stated for all tests. Deriving it from rational points, for
a smooth subgroup over an algebraically closed field, is a separate step and is
not proved here.
