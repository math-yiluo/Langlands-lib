# Naturality of the componentwise pushout tensor map

Module `Langlands.Algebra.PushoutCechNaturality`, namespace
`Langlands.Algebra.PushoutIdealTensor`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). It is pure algebra in one universe `u` and adds to the Library module
`Langlands.Algebra.PushoutIdealTensor`. Everything is proved in the file, with no
hypotheses beyond those in the signatures.

The geometric use: `Γ i` are the rings of sections of a flat relative scheme over
the finite intersections of an affine cover, and `Γ' i` their base changes to a
test ring `A`. Then `cechTensorMap Γ Γ' j` sends base-changed Čech cochains with
coefficients in a module `M` to Čech cochains of the base-changed scheme. This
module shows that the map is compatible with test-ring morphisms, with Čech
differentials and with products. It also shows that finiteness of cohomology
transfers along isomorphisms of complexes.

## `Naturality` section

Data, as in the `Cech` section of `PushoutIdealTensor`: commutative rings
`C, A, A', A₀`, algebras `C → A`, `C → A'`, `C → A₀`, `A₀`-modules `M`, `M'` with
compatible `C`-module structures, a finite index type `ι` with decidable equality,
and families of commutative rings `Γ i`, `Γ' i`, `Γ'' i`. Each `Γ i` is a
`C`-algebra. `Γ' i` is a `Γ i`- and an `A`-algebra with
`Algebra.IsPushout C A (Γ i) (Γ' i)` and the scalar towers. `Γ'' i` is a
`Γ i`- and an `A'`-algebra with `Algebra.IsPushout C A' (Γ i) (Γ'' i)` and the
scalar towers. Finally `j : M →ₗ[C] A` and `j' : M' →ₗ[C] A'`.

- `cechTensorMap_natural h H hHA hHΓ φ hφ y i`: let `h : A →+* A'` and
  `H i : Γ' i →+* Γ'' i` be ring maps. Suppose `H i` is compatible with the
  algebra maps from `A` and `A'` along `h` (`hHA`) and with the algebra maps from
  `Γ i` (`hHΓ`). Let `φ : M →ₗ[A₀] M'` satisfy `j' (φ m) = h (j m)`. Then
  `H i (cechTensorMap Γ Γ' j y i) = cechTensorMap Γ Γ'' j' (φ.lTensor _ y) i`.
  Proof: induction on tensors, then `cechTensorMap_tmul` on both sides.
- `cechTensorMap_differential Γ₁ Γ₁' D D' hD y`: take a second family `Γ₁ t`,
  `Γ₁' t` over a finite index type `κ` with the same structure. Take a `C`-linear
  map `D : (∀ i, Γ i) → (∀ t, Γ₁ t)` and an `A`-linear map
  `D' : (∀ i, Γ' i) → (∀ t, Γ₁' t)`. Assume `D'` applied to the componentwise
  image of `x` equals the componentwise image of `D x` (`hD`). Then
  `cechTensorMap Γ₁ Γ₁' j ((D.baseChange A₀).rTensor M y) = D' (cechTensorMap Γ Γ' j y)`.
  Proof: on `(a ⊗ x) ⊗ m` the value of `cechTensorMap` is the scalar
  `j (a • m) ∈ A` times the componentwise image of `x`. Then use `A`-linearity of
  `D'` and `hD`.
- `cechTensorMap_mul_eq_zero hj y y' i`: if `j m * j m' = 0` for all `m, m'`,
  then `cechTensorMap Γ Γ' j y i * cechTensorMap Γ Γ' j y' i = 0`. Proof: by
  biadditivity it suffices to treat simple tensors. Their product is the image
  of `j (a • m) * j (a' • m') = 0` times an element of `Γ' i`.

## `Finiteness` section

Data: a commutative ring `A` and two sequences of `A`-modules `C i`, `C' i`
(`i : ℕ`) with `A`-linear maps `d i : C i → C (i + 1)`,
`d' i : C' i → C' (i + 1)`. The lemmas also take `A`-linear equivalences
`e i : C i ≃ C' i` with `e (i + 1) (d i x) = d' i (e i x)` (`he`).

- `FiniteCohomology d : Prop` (a definition): `ker (d 0)` is a finite
  `A`-module, and for every `i` so is
  `ker (d (i + 1)) ⧸ (range (d i)).comap (ker (d (i + 1))).subtype`. This is the
  cohomology-finiteness hypothesis of
  `Langlands.Cohomology.ModuleComplex.ObstructionCone.OpenStatement`, in the same
  form. The definition keeps the instances generic in `C`. So a later
  application of `OpenStatement` to a concrete complex never has to synthesize
  quotient instances on kernels.
- `finite_ker_of_equiv`: if `ker (d' 0)` is finite, so is `ker (d 0)`. Proof:
  `(e 0).symm` restricts to a surjection `ker (d' 0) → ker (d 0)`.
- `finite_homology_of_equiv i`: if the degree `i + 1` cohomology of `(C', d')` is
  finite, so is that of `(C, d)`. Proof: `(e (i + 1)).symm` restricts to kernels,
  maps the boundaries of `d'` into those of `d`, and the induced map of quotients
  (`Submodule.mapQ`) is surjective.
- `finiteCohomology_of_equiv`: `FiniteCohomology d' → FiniteCohomology d`, from
  the two previous lemmas.

## Provenance

Internal commutative algebra derived from the Library's
`Langlands.Algebra.PushoutIdealTensor` and Mathlib's tensor product and quotient
interfaces. No literature statement is formalized. `FiniteCohomology` restates
the finiteness hypotheses of the Library's `ObstructionCone.OpenStatement`.
