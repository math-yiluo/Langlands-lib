# Uniform point bounds from zero-dimensional generic fibres

Lean module: `Langlands.AlgebraicGeometry.LangWeil.CurvePlaneZeroDimensional`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

This module is a helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581). It
contains elementary commutative algebra: no statement here is a cited theorem of the
literature; all are standard facts proved directly in Lean.

## Zero-dimensional generic fibres

Let `A` be a domain with fraction field `K` (`IsFractionRing A K`) and `D` an `A`-algebra.

- `exists_polynomial_of_finite_tensor`: if `K ⊗[A] D` is a finite-dimensional `K`-vector
  space, every `x : D` satisfies `c • Q(x) = 0` for some polynomial `Q : A[X]` with nonzero
  leading coefficient and some nonzero `c : A`.

  *Proof.* `1 ⊗ x` is integral over `K`; clearing denominators of its minimal monic
  polynomial (`IsLocalization.integerNormalization`) gives `Q` with leading coefficient a
  nonzero `b`, and `Q(1 ⊗ x) = 0` in `K ⊗[A] D = (A∖0)⁻¹ D`, so a nonzero `c` kills
  `Q(x)` in `D`.

- `exists_card_algHom_le_of_krullDimLE_zero`: if `D` is of finite type over `A` and
  `K ⊗[A] D` has Krull dimension zero, there are a nonzero `a : A` and `N : ℕ` such that for
  every field `κ` with an `A`-algebra structure in which `a` maps to a nonzero element, the
  set of `A`-algebra maps `D → κ` is finite with at most `N` elements.

  *Proof.* An algebra of finite type over the field `K` with Krull dimension zero is finite
  over `K` (`Module.finite_iff_krullDimLE_zero`). Choose a finite generating set `s`
  of `D` and, for each generator, the data `Q, c` above. Take `a` to be the product of all
  `c` and all leading coefficients, and `N` the product of the degrees. If `a ↦ a' ≠ 0` in
  `κ`, every `A`-algebra map `φ : D → κ` sends each generator to a root of the image of its
  `Q` in `κ[X]`, which is a nonzero polynomial of the same degree. Since `φ` is determined
  by the generators, `φ ↦ (φ(x))_{x ∈ s}` injects into a product of root sets, whose size
  is at most `N`.

- `exists_card_algHom_le_of_fiber_krullDimLE_zero`: the same conclusion over an arbitrary
  prime `p` of an arbitrary commutative ring `A`. If `D` is of finite type over `A` and the
  fibre `p.ResidueField ⊗[A] D` has dimension zero, there are `a ∉ p` and `N` such that every
  field `κ` with an `A`-algebra structure that kills `p` and does not kill `a` has at most
  `N` points `D →ₐ[A] κ`.

  *Proof.* Apply the previous theorem to the domain `A ⧸ p`, its fraction field
  `p.ResidueField` and the algebra `(A ⧸ p) ⊗[A] D`, using
  `Algebra.TensorProduct.cancelBaseChange` to identify the fibres. The element `a` is any
  lift of the nonzero element of `A ⧸ p`. A field killing `p` is an `A ⧸ p`-algebra, and
  `Algebra.TensorProduct.liftEquivRight` identifies `A`-algebra maps `D → κ` with
  `A ⧸ p`-algebra maps `(A ⧸ p) ⊗[A] D → κ`.

## Cutting a curve by one function

- `krullDimLE_zero_quotient_span_singleton`: in a commutative ring `T` with prime nilradical
  and Krull dimension at most one, the quotient by a non-nilpotent element `y` has
  dimension zero. *Proof.* A minimal prime `J` over `y` is either minimal in `T`, hence
  equal to the nilradical, which would make `y` nilpotent, or maximal.

- `fiber_quotient_krullDimLE_zero`: for an `A`-algebra `R`, an arbitrary commutative
  `A`-algebra `L` such that `L ⊗[A] R` has prime nilradical and dimension at most one, and
  `h : R` with `1 ⊗ h` not nilpotent, the fibre `L ⊗[A] (R ⧸ (h))` has dimension zero.
  *Proof.* `Algebra.TensorProduct.tensorQuotientEquiv` identifies it with
  `(L ⊗[A] R) ⧸ (1 ⊗ h)`; apply the previous lemma.

- `fiber_krullDimLE_zero_of_subsingleton`: if `L ⊗[A] R` is the zero ring, so is
  `L ⊗[A] (R ⧸ I)` for every ideal `I`, which therefore has dimension zero.

These are used to bound the points of a curve family that lie on a hypersurface `h = 0`
which does not contain a component of the fibre.
