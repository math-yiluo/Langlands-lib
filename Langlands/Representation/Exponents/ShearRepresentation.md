# The shear representation and a `𝔾_m` example for Renard VII.2.6, Remark

Author: Worker 128. Module `Langlands.Representation.Exponents.ShearRepresentation`.

This helper module builds a counterexample for Renard's Remark after the Corollary of VII.2.6.
The Corollary says that an irreducible tempered representation is unitary. The Remark says that
without irreducibility the conclusion can fail, but Renard gives no example. The example used
here, `𝔾_m` acting on `ℂ²` by `x ↦ [[1, ord(x)], [0, 1]]`, is a standard reducible,
indecomposable representation. Its choice is ours; it is not taken from the source.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, registered
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VII.2.6, Remark
(printed p.232 / PDF p.238). The definitions below are internal constructions that realize
this example. They are not definitions taken from the source, which states the Remark without
an example.

## General shear representation (namespace `Langlands.ShearRepresentation`)

- `shear a` is the `ℂ`-linear map `(x, y) ↦ (x + a y, y)` on `ULift.{v} (ℂ × ℂ)`. The lift
  places the carrier in the arbitrary universe `v` that `SmoothRep.{0, u, v}` requires.
  `shear_zero` and `shear_add` give `shear 0 = id` and `shear (a + b) = shear a ∘ shear b`.
- `shearRep φ`, for a group `Γ` and a homomorphism `φ : Γ →* Multiplicative ℂ` (an additive
  character `Γ → ℂ`), is the representation `g ↦ shear (φ g)`, that is, the matrix
  `[[1, φ(g)], [0, 1]]`.
- `sq_shearRep_sub_one`: each operator is unipotent, `(shearRep φ g - 1)² = 0`, because
  `shear a - 1` sends `(x, y)` to `(a y, 0)`, and applying it again gives `(a · 0, 0) = 0`.
- `not_isUnitarizable_shearRep`: if `φ(g) ≠ 0` for some `g`, then there is no invariant positive
  definite Hermitian form (`IsUnitarizable`). Put `e₁ = (1, 0)` and `e₂ = (0, 1)`. Then
  `g e₁ = e₁` and `g e₂ = φ(g) e₁ + e₂`. Invariance gives `⟨g e₂, g e₁⟩ = ⟨e₂, e₁⟩`, and
  additivity and conjugate-linearity in the left slot (`add_left`, `smul_left`) turn this into
  `conj(φ(g)) ⟨e₁, e₁⟩ = 0`. Hence `⟨e₁, e₁⟩ = 0`, and definiteness gives `e₁ = 0`, which is
  false.
- `isSmooth_shearRep`: if an open subgroup `K` lies in the kernel of `φ`, then `K` fixes every
  vector, so the representation is smooth (`IsSmooth`).
- `isAdmissible_shearRep`: under the same hypothesis the representation is admissible
  (`IsAdmissible`). Every space of fixed vectors is a submodule of the finite-dimensional
  `ULift (ℂ × ℂ)`, so it is finite (Mathlib's `Module.Finite` instances for `ULift` and for
  submodules over a field).

## The multiplicative group (namespace `Langlands.ShearRepresentation.Gm`)

For a nonarchimedean local field `k`:

- `group k` is `(Gm (Spec k)).toGrp`, and `isConnectedReductive` holds because it is a split
  torus (`isSplitTorus_gm`, `IsSplitTorus.isConnectedReductive`).
- `identityCharacter k` is the identity rational character `𝟙 : 𝔾_m ⟶ 𝔾_m`.
- `gmValuation k : 𝔾_m(k) →* Multiplicative ℂ` sends `g` to the integer
  `(Plancherel.rationalCharacterValuation (group k) g)` evaluated at the identity character,
  cast to `ℂ`. This is the published integer order of the value of that character, that is
  `ord(x)` for `x ∈ kˣ`.
- `gmValuation_eq_one_of_mem`: `gmValuation` is trivial on the published common norm kernel
  `Plancherel.rationalCommonNormKernel` (by `mem_rationalCommonNormKernel_iff_valuation`).
- `uniformizerPoint k` is the point of `𝔾_m(k)` corresponding to the uniformizer unit
  `SplitTorusValuation.uniformizerUnit k` (through `Gm.affinePointsEquiv`).
  `gmValuation_uniformizerPoint` says its value is `1`. The character value is the uniformizer
  itself (`rationalCharacterEval_apply`, `Category.comp_id`), whose order is `1`
  (`SplitTorusValuation.fieldOrderUnits_uniformizerUnit`).
- `mul_comm_rationalPoints`: `𝔾_m(k)` is commutative, via `Gm.affinePointsEquiv` onto
  `kˣ`.
- `isSmooth_shearRep_gmValuation` and `isAdmissible_shearRep_gmValuation`: for the canonical
  evaluation topology `RationalPointFamily.pointTopology`, the open subgroup is the published
  `Plancherel.rationalCommonNormOpenSubgroup`. Its openness is
  `Plancherel.isOpen_rationalCommonNormKernel`.
- `not_isUnitarizable_shearRep_gmValuation`: the representation is not unitarizable, because
  `gmValuation` takes the value `1 ≠ 0` at the uniformizer point.
