# Waldspurger VIII.1.1: surjectivity of the actual synthesis `κ`

This module states Théorème VIII.1.1 as Prop-valued targets: for fixed construction
data, for one group, and for all groups. It proves only that (1) and (2) of VIII.1
together give surjectivity. It does not prove VIII.1.1. It does not prove the converse
either: that direction needs the second assertion of VII.2.5, which this module does
not import.

Namespace: `Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion`.
The module imports `RationalSemistandardFourierReconstruction`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`), Théorème VIII.1.1,
printed p. 320 (PDF p. 86): "L'application κ est surjective." The map is
`κ : C^∞(Θ)_inv → C(G)` of VII.2. The same page says that, by Théorème VII.2.5, the
theorem is equivalent to (1) and (2) together. The codomain `C(G)` is the
Harish-Chandra Schwartz space of III.6 (printed p. 271), defined with the height of
I.1 (printed p. 242), which comes from an algebraic embedding into `GL_n` mapping `K`
into `GL_n(O_F)`.

## Targets

- `SynthesisSurjectivityStatement`: for fixed data, the actual synthesis
  `GlobalSynthesis.invariantSynthesis` is surjective onto the Harish-Chandra
  Schwartz space `RationalSchwartzSpace`. The fiber-finiteness argument of `κ` is the
  proved `semistandardSpectralFiberFiniteness`, and the presentations are
  `C.presentation`, as in the Library's VII.2.4 formulas. The construction inputs
  are those of `κ`: the source data `a ha mu d C hindex Q K0 hK0`, the compacts
  `hspecial hd hQ`, and the VI.3.1 Schwartz membership witness
  `hsynth : SchwartzMembershipStatement …`. No surjectivity, reconstruction, Fourier
  support or orbit finiteness for `G` is an input.
  `synthesisSurjectivityStatement_iff_range` restates it as `LinearMap.range κ = ⊤`.
- `RationalLocalSynthesisSurjectivityStatement G`: for one field `F` and one group `G`
  (affine, locally of finite type), for every connected reductivity proof and all
  source data with the I.1 normalizations, `κ` is surjective. One compact `K` is the
  source special compact (`IsSourceCompactAt i K`). It serves as the Schwartz compact,
  as `Kbase` and `K0` of `κ`, and, through `hd` and `hQ`, as the compact of every
  compact picture and scalar datum. The height comes from a matrix representation
  `rho` that is a closed embedding (`IsClosedSubgroup rho`) with `K` in its integral
  subgroup (`K ≤ rationalHeightSubgroup rho`), as in I.1 (printed p. 242), so the
  codomain is the Schwartz space `C(G)` of III.6 (printed p. 271). This premise matters:
  for the trivial representation of `G_m`, the height vanishes and `Ξ = 1`, so the
  constant function `1` lies in `RationalSchwartzSpace` but not in `C(G)`. The split-central quotient Haar measures satisfy
  `WavePacketPairing.SourceLeviQuotientHaar` for `K`. The field may have positive
  characteristic. The group need not be quasi-split, and its rank may be zero. The
  carrier universe is independent of the field universe.
- `RationalSynthesisSurjectivityStatement`: the closure over all fields and groups.

## Proved relations

- `synthesisSurjectivity_of_fourierInversion`: `FourierInversionStatement` gives
  surjectivity. Each `f` is `κ` of its own invariant Fourier lift.
- `synthesisSurjectivity_of_lift_of_reconstruction`: the same from the separate
  targets `FourierInvariantLiftStatement` and `SynthesisReconstructionStatement`.

## Input ledger

- Structural data: the maximal split torus and generic cocharacter, the Iwasawa pair,
  the split components with their instances, the compact data with `hd`, the finite
  index `hindex`, the packet data `Q` with `hQ`, and the comparison data `C`
  (`WeylSectionComparisonData`).
- Normalizations in the local target: the source height (`IsClosedSubgroup rho`,
  `K ≤ rationalHeightSubgroup rho`), `IsSourceCompactAt` and `SourceLeviQuotientHaar`.
  The fixed-data target `SynthesisSurjectivityStatement` allows any `rho`; the local
  target is its source specialization.
- Preceding construction input of `κ`: the VI.3.1 membership witness `hsynth`.
- Remaining analytic assertion: VIII.1.1 itself.

## Declaration-level dependency map

- `SynthesisSurjectivityStatement` → `GlobalSynthesis.invariantSynthesis`,
  `GlobalSynthesis.SchwartzMembershipStatement`, `semistandardSpectralFiberFiniteness`.
- `synthesisSurjectivity_of_fourierInversion` → `surjective_of_fourierInversion`.
- `synthesisSurjectivity_of_lift_of_reconstruction` → `fourierInversionStatement_iff`.
- `RationalLocalSynthesisSurjectivityStatement` → `IsSourceCompactAt`,
  `WavePacketPairing.SourceLeviQuotientHaar`.
