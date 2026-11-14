# Picard classes of relative effective divisors under base change

Authors: Worker 22.

Worker 22 wrote this helper module for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). It is part of the proof
of `PicardHilbertPiecesRepresentabilityReductionStatement`; the main theorem
and the full route are in `PicardHilbertPiecesRepresentabilityReductionProof.md`.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction`.

Provenance: internal. The module computes how the class of the divisor line
bundle `O(D)` behaves under flat base change and under arbitrary base change.
Kleiman discusses base change of relative effective divisors after
Definition 3.6 (*The Picard scheme*, p.23). The arbitrary case is taken from
the hypothesis `RelativeEffectiveDivisorBaseChangeStatement` of the
reduction.

## Divisor classes

- `pb_comp_apply`: `Group.pullback (a ≫ b) x = Group.pullback a (Group.pullback b x)`.
- `dcl I hI`: the class of the divisor line bundle
  `EffectiveCartierDivisor.lineBundle ⟨I, hI⟩` of an effective Cartier ideal
  `I`. `dcl_congr` transports it along an equality of ideals.
- `dcl_eq`: `dcl I = -(class of the ideal line bundle of I)`, by
  `classOf_dual`.
- `dcl_of_kernelIso`: let `φ : Y' ⟶ Y`. If the pullback along `φ` of the
  ideal module (`kernelModule I.subschemeι`) of `I` is isomorphic to the ideal
  module of `J`, then `dcl J = Group.pullback φ (dcl I)`.

## Base change of relative effective divisors

- `isPullback_comap`: the closed subscheme of `I.comap φ` is the pullback of
  the closed subscheme of `I` along `φ` (Mathlib's `IdealSheafData.comapIso`).
- `flat_comap`: let `φ` be flat and `I` a relative effective Cartier ideal for
  `p : Y ⟶ T`. Then `I.comap φ` is relative effective Cartier for `φ ≫ p`, and
  `dcl (I.comap φ) = φ^* dcl I`. The ideal modules are compared by the
  Library's `StructureKernelFlatBaseChange.kernelModuleFlatBaseChangeIso`.
  The flatness of the subscheme over `T` follows from the pullback square.
- `bc_comap`: the same for an arbitrary cartesian square
  `IsPullback h q p g`. It uses `RelativeEffectiveDivisorBaseChangeStatement`
  (hypothesis `hbc`). That statement gives the result for the standard
  pullback `pullback g p`, with an isomorphism of ideal modules. `flat_comap`
  along the isomorphism `Y' ≅ pullback g p` then moves it to `Y'`.

## Families `X ×_S T`

For `f : X ⟶ S` and `h : T' ⟶ T` over `S` (`w : h ≫ s = s'`):

- `mapX f h w : X ×_S T' ⟶ X ×_S T` is the comparison map
  `pullback.map f s' f s (𝟙 X) h (𝟙 _)` that occurs in the statements.
  `mapX_fst`, `mapX_snd` give its projections, and `mapX_comp` composes two
  of them.
- `isPullback_mapX`: the square of `mapX` over `h` is cartesian.
- `divBC`: `bc_comap` for this square. A relative effective divisor on
  `X ×_S T` pulls back along `mapX` to one on `X ×_S T'`, with the pulled-back
  class.
- `pb_mapX_fst`: pulling back a class from `X` to `X ×_S T` and then along
  `mapX` gives its pullback to `X ×_S T'`.
