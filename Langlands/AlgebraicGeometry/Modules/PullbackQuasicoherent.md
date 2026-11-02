# Pullback of module sheaves preserves quasi-coherence

Fix schemes `X Y : Scheme.{u}` in an arbitrary universe `u` and a morphism
`f : X ⟶ Y`. Write `f^*` for Mathlib's module pullback
`AlgebraicGeometry.Scheme.Modules.pullback f`, the left adjoint of the module
pushforward.

## Pulled-back quasi-coherent data

A `SheafOfModules.QuasicoherentData` for `M : Y.Modules` is Mathlib's data
witnessing quasi-coherence: a family of opens `q.X i` of `Y` covering `Y`, and
for each `i` a presentation (cokernel of a map of free modules) of the
restriction `M.over (q.X i)` to the slice site of `q.X i`.

`Langlands.Scheme.Modules.pullbackQuasicoherentData f q` is quasi-coherent data
for `f^*M` with the same index type, opens `f ⁻¹ᵁ q.X i`, and presentations
`Langlands.AlgebraicGeometry.Modules.presentationPullbackOver f M (q.X i)
(q.presentation i)`. That published Library construction (module
`FinitePresentationPullback`) turns a presentation of `M.over U` into one of
`(f^*M).over (f ⁻¹ᵁ U)`, for any open `U` and with no finiteness hypothesis.
The covering condition holds because the inverse images of a cover of `Y`
cover `X`: Mathlib's `Opens.coversTop_iff` translates covering of the top
object into `iSup = ⊤`, and `Scheme.Hom.iSup_preimage_eq_top` pulls this back
along `f`.

## Quasi-coherence

The instance `Langlands.Scheme.Modules.isQuasicoherent_pullback f M` states:
if `M : Y.Modules` is quasi-coherent (`SheafOfModules.IsQuasicoherent`), then
`f^*M` is quasi-coherent. There is no hypothesis on `f`: it holds for every
morphism of schemes. The proof chooses quasi-coherent data for `M` (provided by
`IsQuasicoherent.nonempty_quasicoherentData`), applies
`pullbackQuasicoherentData`, and concludes with Mathlib's
`QuasicoherentData.isQuasicoherent`.

## Provenance and scope

This is an internal helper: the classical fact that pullback preserves
quasi-coherence. It drops the finiteness part of the published
`isFinitePresentation_pullback` proof and assembles the rest from pinned
Mathlib (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`,
`Mathlib/CategoryTheory/Sites/Spaces.lean`,
`Mathlib/AlgebraicGeometry/Scheme.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`). It generalizes the published
`isQuasicoherent_affinePullback` (the case `f = Spec.map φ`) to arbitrary `f`.
It asserts nothing about finite type, finite presentation, coherence, or
cohomology of the pullback.
