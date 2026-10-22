# Proof of the admissible Hermitian identification clause

Author: Worker 249.

The closing theorem
`Langlands.Classification.unitaryAdmissibleHermitianClause` proves exactly the
published proposition
`Langlands.Classification.UnitaryAdmissibleHermitianClause.{uF, uV} F T` of
[UnitaryGenericCompatibilityStatement.md](UnitaryGenericCompatibilityStatement.md).
Its parameters are an arbitrary prime `p`, an actual p-adic field
`F : PadicField.{uF} p` and a topological realization `T : F.TopologicalData`.
The field universe `uF` and the representation-carrier universe `uV` are
independent. The theorem has no other hypotheses, and the statement module,
its Markdown and the modules it imports are unchanged.

## Statement proved

For every positive rank `n`, with the topology and topological-group structure
on `GL_n(F)` supplied by `T`, and for every smooth complex representation `δ`
with carrier in universe `uV` that is admissible, and for every invariant
positive form `b` on `δ`, there is a conjugate-linear equivalence
`E : δ ≃ₗ⋆[ℂ] SmoothDual δ.representation` such that

- `E (δ g v) = smoothContragredient δ g (E v)` for every `g` and `v`, and
- `smoothDualPairing δ (E v) w = b.inner v w` for every `v` and `w`.

The proof assumes nothing about `δ` beyond the hypotheses of the clause: no
irreducibility, square-integrability, finite-dimensionality, Hilbert
completion or norm on the carrier.

## Implemented proof

After introducing `n`, the positivity hypothesis, `δ`, admissibility `hδ` and
`b`, the proof installs `T.topology` and `T.generalLinearTopologicalGroup n` as
local instances, exactly as the statement's `letI` bindings do. It then takes

`E = b.smoothDualEquiv (GeneralLinear.compactOpen_cofinal F T n) hδ`.

`InvariantPositiveForm.smoothDualEquiv` is the generic construction of
[HermitianDual.md](../Unitary/HermitianDual.md): the equivalence
`v ↦ b(v, -)` onto the smooth dual. It is defined for any topological group in
which compact open subgroups are cofinal among open subgroups, and any
admissible representation. The published theorem
`GeneralLinear.compactOpen_cofinal F T n` supplies cofinality for `GL_n(F)`.
The two required identities are:

- equivariance, `InvariantPositiveForm.toSmoothDual_apply_action`, because
  `smoothDualEquiv` applies as `toSmoothDual` by definition;
- the pairing identity, which holds by `rfl`: the smooth dual pairing evaluates
  the functional `b(v, -)` at `w`.

The positivity hypothesis `0 < n` is not used. The generic construction works
for every rank.

## Route

The proof follows the route suggested in the task. Smoothness and equivariance
of `b(v, -)` come from invariance of `b`, and injectivity from definiteness.
Surjectivity combines finite-dimensional Riesz representation on a compact-open
fixed space with the published compact fixed-space duality
`smoothDualFixedRestriction_bijective`, which is proved by compact-open
averaging. Details are in [HermitianDual.md](../Unitary/HermitianDual.md).
