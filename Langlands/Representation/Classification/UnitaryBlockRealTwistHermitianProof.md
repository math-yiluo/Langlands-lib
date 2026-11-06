# Hermitian duality of real twists of unitary blocks

Author: Worker 1431.

The theorem
`Langlands.Classification.unitaryBlockRealTwistHermitianClause` proves exactly
the published proposition
`Langlands.Classification.UnitaryBlockRealTwistHermitianClause.{uF, uV} F T`
from
[UnitaryGenericCompatibilityStatement.md](UnitaryGenericCompatibilityStatement.md).
It applies to every prime, actual finite p-adic field `F` and compatible
topological realization `T`, with independent field and carrier universes.
The statement and its import closure are unchanged.

For every positive rank, irreducible analytically square-integrable smooth
block `δ`, invariant positive Hermitian form `b` on `δ`, and real exponent
`s`, the theorem supplies a conjugate-linear equivalence

`E : δ ≃ₗ⋆[ℂ] SmoothDual (T.segmentFactor δ s).representation`.

It intertwines the source action `ν^(-s) δ` with the smooth dual action of
`ν^s δ`, and satisfies `E(v)(w) = b.inner v w`. The form is conjugate-linear
in its first variable. The smooth dual is the smooth-vector submodule of the
algebraic dual, with action `g · ℓ = ℓ ∘ δ(g⁻¹)`.

The implementation first uses
`PadicField.TopologicalData.IsSquareIntegrable.isAdmissible` to obtain
admissibility. Compact open subgroups are cofinal by
`GeneralLinear.compactOpen_cofinal`, so
`InvariantPositiveForm.smoothDualEquiv` gives the conjugate-linear equivalence
`H(v) = b(v, -)` onto `SmoothDual δ.representation`. It then takes the
published ordinary duality comparison
`D = segmentFactorSmoothDualEquiv F T δ s` and defines
`E = H.trans D.symm.toLinearEquiv`. This comparison identifies the smooth
dual of `ν^s δ` with `ν^(-s) δ^∨` while keeping each underlying functional.

For equivariance, semilinearity of `H` conjugates the scalar
`|det(g)|^(-s)`. This scalar is real, so `Complex.conj_ofReal` fixes it.
`InvariantPositiveForm.toSmoothDual_apply_action` then gives equivariance
into `ν^(-s) δ^∨`, and the intertwining property of `D.symm` gives the
required final action. The evaluation identity is definitional: both
comparisons keep the functional `w ↦ b.inner v w`.

The proof uses no classification or exponent bounds. Positivity of the rank
and irreducibility are retained from the exact statement but are not needed
by this construction. It does not supply unitary generic exhaustion or
same-block multiplicity symmetry.

The original correspondence is Tadic 1986, §2.1 (printed p.345, PDF p.12),
which distinguishes Hermitian contragredience and ordinary duality, and
§§5.3–5.5 (printed p.362, PDF p.29), which give their opposite-exponent
formulas for unitary blocks. The prescribed evaluation identity is a concrete
refinement implemented using the published admissible-form construction.
The registered source is `tadic-1986-unitary`, SHA256
`08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`.
