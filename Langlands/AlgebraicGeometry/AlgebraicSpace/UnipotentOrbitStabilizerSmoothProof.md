# Stabilizers of unipotent actions with constant orbit dimension are smooth

Author: Worker 5434.

The theorem `Langlands.AlgebraicGeometry.AlgebraicSpace.unipotentOrbitStabilizerSmooth.{u}`
proves the unchanged published proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStabilizerSmoothStatement.{u}`
(`Langlands/AlgebraicGeometry/AlgebraicSpace/UnipotentOrbitStabilizerSmoothStatement.lean`)
for an arbitrary universe `u`. No hypothesis is added. The proposition says the following.
Let `k : Type u` be a field of characteristic zero and `G` a group scheme over `Spec k` that
is affine, locally of finite type and unipotent (`IsUnipotent G`). Let `b` be an action of `G`
on a reduced scheme `Z` locally of finite type over `k`, and let `d : ℕ` with
`HasOrbitDimension b z d` for every point `z` of `Z`. Then the projection to `Z` of the
stabilizer scheme, `pullback.snd (lift b.hom (snd G.X Z)) (lift (𝟙 Z) (𝟙 Z))`, is smooth.

The kernel inspection of the theorem reports only the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## The proof

The proof is one application of three published Library declarations:

```lean
theorem unipotentOrbitStabilizerSmooth : UnipotentOrbitStabilizerSmoothStatement.{u} :=
  unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected
    GroupScheme.reducedBaseConnectedFibreSmooth GroupScheme.charZeroUnipotentConnected
```

- `Langlands.AlgebraicGeometry.AlgebraicSpace.unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected`
  (module `Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStabilizerSmoothReduction`)
  has type
  `ReducedBaseConnectedFibreSmoothStatement.{u} → CharZeroUnipotentConnectedStatement.{u} →
  UnipotentOrbitStabilizerSmoothStatement.{u}`. Its proof treats the stabilizer scheme as a
  group scheme over `Z`. Each fibre is a closed subgroup of the base change of `G` to the
  residue field, so it is unipotent (Milne 14.9 and 14.7, proved in the Library). It is smooth
  by Cartier's theorem (Milne 3.23, proved in the Library) and connected by the second
  hypothesis. `HasOrbitDimension` makes the fibre dimension constant. `Z` is reduced and, being
  locally of finite type over a field, locally Noetherian. The first hypothesis then gives
  smoothness.
- `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth`
  (module `Langlands.GroupScheme.ReducedBaseSmoothProof`) proves
  `Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement.{u}`. This is SGA 3,
  Exposé VI_B, Corollaire 4.4, for a reduced locally Noetherian base and connected fibres: a
  group scheme locally of finite type whose fibres are smooth, connected and of locally
  constant dimension is smooth.
- `Langlands.GroupScheme.charZeroUnipotentConnected`
  (module `Langlands.GroupScheme.Unipotent.CharZeroConnectedProof`) proves Milne,
  Corollary 14.15: an affine unipotent group scheme locally of finite type over a field of
  characteristic zero has connected underlying space. It is a proof-producing `def` that writes
  out the quantifiers of `Langlands.GroupScheme.CharZeroUnipotentConnectedStatement.{u}`. The
  two types agree definitionally, and the application above type-checks.

All three are used in the same universe `u` as the target.

## Relation to the sources

This is the derivation in the Markdown of `UnipotentOrbitStabilizerSmoothStatement`
(steps 1–4): SGA 3, Exposé VI_B, Corollaire 4.4 over a reduced base, together with Cartier's
theorem and Milne 14.7, 14.9 and 14.15. The Library proof of SGA 3 VI_B 4.4 does not follow
the printed route through EGA IV₃ 15.6.7. Its Markdown,
`Langlands/GroupScheme/ReducedBaseSmoothProof.md`, describes the route it takes. The
declaration name `unipotentOrbitStabilizerSmooth` is the project's (provenance: derived).
