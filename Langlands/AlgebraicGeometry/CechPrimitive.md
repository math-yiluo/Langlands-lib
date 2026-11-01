# Primitivity of degree-one Čech cocycles for a multiplication with two-sided unit

Author: Worker 274.

This module proves that degree-one Čech cocycles of the structure sheaf are primitive for a
multiplication `m : X ×_R X ⟶ X` with a two-sided unit over a field `R`: `m^* z` and
`p₁^* z + p₂^* z` differ by a Čech coboundary on a common refinement. It is a helper for the
proof of `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`. It contains no
`sorry` and no new axioms.

## Provenance

That `m^* x = p₁^* x + p₂^* x` for `x ∈ H¹(A, 𝒪_A)` of an abelian variety is the primitivity of
degree-one classes used in the registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, (6.12)–(6.15), printed pp. 92–94; it
follows from the injectivity of `H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` on classes killed by both
axes, which is the Library theorem
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.exists_coboundary_of_axes`
(a Čech-level statement for the product cover). This module transfers the difference
`m^* z - p₁^* z - p₂^* z` to the product cover and checks the axis conditions at the Čech level.
Its exact form is a project choice.

## Definitions

All declarations are in namespace `Langlands.Cohomology.Cech`.

- `pair w a b : Γ(P, V a ⊓ V b)`, for a `1`-cochain `w` of `𝒪_P` on `V`, is `w (a, b)` viewed on
  `V a ⊓ V b` (the form of cocycles used by the Library two-axis theorem).
- `primCover p₁ p₂ m U (ab, c) = p₁⁻¹ U ab.1 ⊓ p₂⁻¹ U ab.2 ⊓ m⁻¹ U c` (abbreviation).

## Results

- `pull_congr`: pullbacks along equal morphisms agree.
- `refine_pull`, `pull_refine`: refining a pullback, or pulling back a refinement, is a pullback
  with the composite index map.
- `pull_const_eq_zero`: the pullback of a `1`-cocycle with a constant index map is `0`
  (cocycles vanish on constant pairs).
- `inter_one`: `inter V σ = V (σ 0)` for `σ : Fin 1 → κ`.
- `pair_cocycle`: for a `1`-cocycle `w`, `pair w` satisfies the cocycle identity in the form of
  the Library two-axis theorem.
- `exists_d_eq_of_pair`: if `pair w a b = y b - y a` on `V a ⊓ V b` for sections `y a` on `V a`,
  then `w` is a coboundary.
- `exists_axis_of_d_eq`: if the pullback of `w` along `i : X ⟶ P` is a coboundary for the cover
  `i⁻¹ V`, then `w` satisfies the axis hypothesis of the Library two-axis theorem for `i`.
- `iSup_primCover`: if `U` covers `X`, `primCover p₁ p₂ m U` covers `P`.
- `exists_pull_axis_eq_d`: on an axis `i` with `i ≫ m = 𝟙`, `i ≫ q = 𝟙` and
  `i ≫ q' = πX ≫ e`, the pullback along `i` of `m^* z - (q^* z + q'^* z)` is a coboundary
  (`pull_sub_pull_eq_d` for the two identity pullbacks, `pull_const_eq_zero` for the third).
- `exists_pull_sub_refine_eq_d` (primitivity): let `R` be a field, `P` a fibre product of
  `πX : X ⟶ Spec R` with itself (`IsPullback p₁ p₂ πX πX`), all global functions on `X` come from
  `R` (`Function.Surjective (secHom πX ⊤).hom`), `m : P ⟶ X`, `e : Spec R ⟶ X` with
  `e ≫ πX = 𝟙`, and axes `i₁, i₂ : X ⟶ P` with `i₁ ≫ p₁ = 𝟙`, `i₁ ≫ p₂ = πX ≫ e`,
  `i₂ ≫ p₁ = πX ≫ e`, `i₂ ≫ p₂ = 𝟙`, `i₁ ≫ m = 𝟙`, `i₂ ≫ m = 𝟙`. Let `U` be a finite cover of
  `X` by affine opens with affine pairwise intersections and `z` a `1`-cocycle of `𝒪_X` on `U`.
  Then on `primCover p₁ p₂ m U` the pullback `m^* z` minus the refinement of
  `p₁^* z + p₂^* z` from the product cover is a coboundary. Proof: the difference `w` is a
  cocycle; degree-one refinement surjectivity (`CechShift.exists_refine_sub_eq_d`, for the
  Čech-acyclic structure sheaf) gives `w'` on the product cover with `refine w' - w = d g`; the
  pullbacks of `w'` to both axes are coboundaries by `exists_pull_axis_eq_d` and degree-one
  refinement injectivity on `X` (`Cech.exists_d_eq_of_refine_eq_d`); the Library two-axis
  theorem makes `w'` a coboundary, hence `w` is one.
