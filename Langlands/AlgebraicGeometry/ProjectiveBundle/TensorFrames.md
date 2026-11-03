# Genuine frames after tensoring with a line bundle

Let `S : Scheme.{u}`, let `M, N : S.Modules` be actual sheaves of modules, and
let `n : ℕ`. This module constructs genuine local frames for `M ⊗ N` wherever
`M` has a frame of size `n + 1` and `N` has a trivialization. If `M` has fixed
local rank `n + 1` and `N` is locally free of rank one, these opens form a basis,
give frame atlases for both `M` and `M ⊗ N`, and prove that the tensor has the
same fixed local rank.

The tensor in these assertions is `Langlands.Scheme.Modules.tensorObj M N`,
the existing sheaf tensor product. The rank-one hypothesis is
`Picard.IsLocallyFreeRankOne N`, which supplies an isomorphism
`N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf` near each point.
No global trivialization is assumed.

## Transport of genuine frames

The existing `LocalFrame M n U` is a sheaf isomorphism

```text
free (ULift (Fin (n + 1))) ≅ M.over U.
```

`LocalFrame.ofRestrictIso e f` transports such a frame along an isomorphism
`f : M.restrict U.ι ≅ N.restrict U.ι`. It first conjugates `f` by the
components of `Scheme.Modules.overFunctorEquiv U`, then takes the preimage
isomorphism under the fully faithful equivalence `Scheme.Modules.overEquiv U`.
Composing with `e` produces a frame of `N.over U`.

`LocalFrame.tensor e t` applies this transport to the inverse of the published
`Modules.tensorRestrictionTrivialization M N U t`. That isomorphism identifies
`(M ⊗ N).restrict U.ι` with `M.restrict U.ι` using tensor restriction,
the given trivialization of `N`, and the tensor right unitor. Thus the
constructed tensor frame is an actual sheaf isomorphism, rather than a
chosen equivalence of section modules on a single open.

## From pointwise frames to fixed local rank

`isLocallyFreeOfRank_of_localFrames` proves that frames of size `n + 1`
on neighborhoods of every point imply `IsLocallyFreeOfRank M (n + 1)`.
This uses the existing rank predicate, whose data are a covering family of
local generators, invertible generator maps, and index sets equivalent to
`Fin (n + 1)`.

For each point, choose one frame-bearing neighborhood. Their inclusions cover
`S` because the chosen neighborhood contains its point. Transport the standard
generating sections of the free sheaf along each chosen frame homomorphism.
`GeneratingSections.ofEpi_π` identifies the new generator map with the
composite of the standard generator map and this isomorphism, so it is
invertible. Each generator index set is `ULift (Fin (n + 1))`;
`Equiv.ulift` supplies the required cardinality witness. The construction
retains the scheme universe `u`.

## A joint basis and its two frame atlases

`TensorFrames.opens M N n` consists of the opens `U` satisfying both

```text
Nonempty (LocalFrame M n U)
Nonempty (N.restrict U.ι ≅ unit).
```

`opens_of_le` shows that this property passes to smaller opens. Restrict the
frame with `LocalFrame.restrict`. For the line trivialization, use the
restriction-to-pullback comparison followed by
`Picard.pullbackTrivializationOfLE`.

Assume `hM : IsLocallyFreeOfRank M (n + 1)` and
`hN : IsLocallyFreeRankOne N`. `exists_open` intersects a frame-bearing
neighborhood supplied by `exists_frameOpen` with a neighborhood trivializing
`N`; this intersection contains the given point and belongs to the joint
collection. `isBasis` further intersects such a neighborhood with any prescribed
open neighborhood. Closure under smaller opens then proves the topological
basis property.

`sourceAtlas hM hN` and `tensorAtlas hM hN` have exactly this same basis.
The former chooses the source frame witnessed on each basis member. The latter
uses `LocalFrame.tensor` with that frame and the witnessed line trivialization.
Both satisfy the published `FrameAtlas` structure, so their frames are genuine
sheaf frames on a covering basis.

Finally, `isLocallyFreeOfRank_tensor hM hN` supplies a tensor frame near every
point using `exists_open` and `LocalFrame.tensor`, and applies the pointwise
frame criterion above. It proves the exact fixed-rank predicate
`IsLocallyFreeOfRank (tensorObj M N) (n + 1)`.

## Provenance and scope

This is a derived construction from the published genuine-frame, sheaf-tensor,
line-trivialization and local-generator APIs, together with Mathlib's
fully faithful equivalences and generating-section transport. It invokes no new
assertion from external literature.

The module does not compare the dual-coordinate cocycles of its two atlases
and does not assert an isomorphism between their projective bundles. Tensor-line
projective invariance, the cubic embedding, the Hilbert quotient, and
`LargeLevelRepresentabilityStatement` remain further obligations.
