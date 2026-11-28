# Components of the relative reduced norm in matrix charts

Module: `Langlands.Algebra.CentralSimple.RelativeNormMatrixChart`, namespace
`Langlands.CentralSimple.UnitaryPoints`.

Throughout, `F ⊆ E` are fields, `B` is a finite-dimensional central simple `E`-algebra that is
an `F`-algebra through `E`, and `relativeNorm F E B R : (R ⊗[F] B)ˣ →* (E ⊗[F] R)ˣ` is the
relative reduced norm of `Langlands.Algebra.CentralSimple.UnitaryPoints`. For an `F`-algebra
map `φ : E → R`, `HermitianMatrix.tensorProj F E φ : E ⊗[F] R → R` is `e ⊗ r ↦ φ(e) r` (module
`Langlands.GroupScheme.Examples.HermitianMatrixSplitting`).

## Definitions

- `tensorQuotient F E B R : R ⊗[F] B →ₐ[R] R ⊗[E] B`, for an `E`-algebra `R` with
  `IsScalarTower F E R`: the natural map `r ⊗ b ↦ r ⊗ b`. `tensorQuotient_tmul` computes it and
  `tensorQuotient_surjective` shows it is surjective.
- `involutionUnits τ R : (R ⊗[F] B)ˣ → (R ⊗[F] B)ˣ` for `τ : FirstKindInvolution F B`: the
  involution `τ_R = τ.baseChange R` on units, with inverse `τ_R(x⁻¹)`. `involutionUnits_eq_inv`:
  on a unitary point (`x τ_R(x) = 1`) it is the inverse.

## Results

- `tensorProj_relativeNorm_eq_reducedNorm`: for an `E`-algebra `R`, the component of the
  relative reduced norm along `e ⊗ r ↦ e r` is the reduced norm over `E` of the image under
  `tensorQuotient`. The proof applies `reducedNorm_naturality` along the `E`-algebra map
  `E ⊗[F] R → R` and checks on pure tensors that this map composed with `tensorEquiv` is
  `tensorQuotient`.
- `reducedNorm_tensorQuotient_eq_det`: let `R` be a field which is an `E`-algebra and
  `C : R ⊗[F] B →ₐ[R] Matrix m m R` a surjective `R`-algebra map sending `1 ⊗ e` to the scalar
  `e`, with `finrank E B = card m * card m`. Then `reducedNorm E B R (tensorQuotient y) =
  det (C y)`. The map `C` descends to an `R`-algebra map `R ⊗[E] B → Matrix m m R`
  (`Algebra.TensorProduct.lift`), surjective because `C` is, hence bijective because both sides
  have dimension `card m * card m` over `R`; the Library's `reducedNorm_eq_chart_det_fintype`
  for this chart gives the determinant.
- `tensorProj_relativeNorm_eq_det`: the combination of the two, stated for an arbitrary
  `F`-algebra map `φ : E → R` (the `E`-algebra structure `φ.toAlgebra` is introduced inside the
  proof): `tensorProj φ (relativeNorm x) = det (C x)` whenever `C` sends `1 ⊗ e` to the scalar
  `φ e`.
- `exists_surjective_chart`: over an algebraically closed field `Ω` with an `F`-algebra map
  `φ : E → Ω`, there is such a chart `Ω ⊗[F] B → Matrix d d Ω`, `d = reducedDegree E B`: a
  splitting chart of `Ω ⊗[E] B` (`exists_matrix_chart_reducedDegree`) composed with
  `tensorQuotient`.
- `algebraMap_matrix_transpose`: scalar matrices are their own transposes.
- `tensorProj_conjugation_relativeNorm`: let `τ` act on `E` by `SU3Root.conjugation F E`. Over
  an algebraically closed `Ω` with `φ : E → Ω`, for a unit `y` of `Ω ⊗[F] B`,
  `tensorProj (φ ∘ conj) (relativeNorm y) = tensorProj φ (relativeNorm (τ_Ω y))`. With `C` from
  `exists_surjective_chart`, the map `C'(w) = (C (τ_Ω w))ᵀ` is again a surjective `Ω`-algebra
  map (two anti-homomorphisms compose to a homomorphism), and it sends `1 ⊗ e` to the scalar
  `φ(ē)`. Applying `tensorProj_relativeNorm_eq_det` to `C'` and to `C`, and `det Mᵀ = det M`,
  gives the identity.
- `mul_conjugation_eq_one`: if `z ⊗ 1` is the relative reduced norm of a unitary point of
  `K ⊗[F] B` for some field `K`, then `z z̄ = 1` in `E`. The unitary point maps to a unitary
  point over `Ω = AlgebraicClosure K` with the same norm (`relativeNorm_naturality`,
  `map_mem_unitaryPoints`); `IsAlgClosed.lift` gives `φ : E → Ω`; since `τ_Ω(x) = x⁻¹`, the
  previous identity gives `φ(z̄) = φ(z)⁻¹`, and `φ` is injective.

## Provenance

Internal. The identity `Nrd(τ x) = conj(Nrd x)` for the relative reduced norm and an involution
of the second kind is the input used in Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), proof of Theorem 6.28, printed p. 364 (PDF p. 374), to obtain `τ(a₀) a₀ = 1`
for the constant term of the characteristic polynomial of a unitary element (relations
(6.44)); source `platonov-rapinchuk-1994-algebraic-groups-number-theory`. The proofs here are
chart computations with the Library's reduced norm and are not taken from a source.
