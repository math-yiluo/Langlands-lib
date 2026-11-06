# Connected reductive groups over finite fields are quasi-split

This module proves `Langlands.GroupScheme.finiteFieldQuasiSplit`, whose type
is exactly `Langlands.GroupScheme.FiniteFieldQuasiSplitStatement.{u}`: for
every finite field `k : Type u` and every group scheme `G` over `Spec k`,
`IsConnectedReductive G` implies `IsQuasiSplit G`.

## Source

Milne, *Algebraic Groups* (corrected 2022 reprint), Section 17k, printed
pp.383–384, Proposition 17.99. Its consequence that connected reductive groups
over finite fields are quasi-split is the result proved here. The registered
source is `milne-2022-algebraic-groups`. The retained author errata
(`milne-2022-algebraic-groups-errata-2026-11-04`) has no correction to this
passage. This module claims only that quasi-splitness consequence. It does not
prove the further statements of Section 17k about maximal tori or Borel pairs.

Milne's argument starts with a Borel subgroup over the algebraic closure. Borel
conjugacy relates it to its Frobenius transform. Lang's theorem then yields a
Frobenius-fixed conjugate, which descends to the finite field. The Lean proof
follows this route.

## Implemented proof

Fix `k`, its `Field` and `Finite` instances, `G` and `hG : IsConnectedReductive G`.

1. Install `Fintype.ofFinite k`. Also install the `Smooth`, `IsAffineHom` and
   `ConnectedSpace` instances supplied by the fields `hG.smooth`,
   `hG.isAffineHom` and `hG.connectedSpace`. Only these three fields are used
   to construct the Borel subgroup. The trivial geometric unipotent radical is
   used only because `IsQuasiSplit` contains the original `hG`.
2. Take `Ω := AlgebraicClosure k`, which is again in universe `u`. The
   canonical base map `algebraBaseMap k Ω` is definitionally the map
   `toAlgebraicClosure k` used by `IsConnectedReductive` and `IsQuasiSplit`.
3. Apply `exists_frobeniusStableBorel_of_borelConjugacy k Ω G` (module
   `Langlands.GroupScheme.Rational.FrobeniusStableBorel`) to the published
   general Borel-conjugacy theorem `Langlands.GroupScheme.borelConjugacy`
   (module `Langlands.GroupScheme.Absolute.BorelConjugacyProof`), instantiated
   at universe `u`, whose type is `BorelConjugacyStatement.{u}`. This gives an
   actual group scheme `B` over `Ω`, an actual inclusion `i : B ⟶ G_Ω` with `IsBorelSubgroup i`, and an
   all-test equality: `SubgroupFunctor.galoisTransport` along the arithmetic
   Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic k Ω` maps
   `SubgroupFunctor.range i` to itself. That helper uses Borel existence and
   conjugacy over `Ω`. It also uses the generic Lang conjugator from
   `Torus.FrobeniusConjugate`, which needs no torus hypothesis.
4. Apply `isQuasiSplit_of_borel_frobeniusTransport_eq hG hi hF` (module
   `Langlands.GroupScheme.Absolute.FrobeniusBorelDescent`). It converts the
   all-test Frobenius invariance into canonical-overlap range equality. This
   uses `Descent.GaloisInvariantClosedSubgroups` and Frobenius approximation on
   finite coefficient sets. It then builds actual `GeometricBorelDescentData i`
   via `Absolute.GeometricBorelDescent`. Those data contain a ground-field group
   scheme, an actual inclusion into `G` and a recovery isomorphism of its
   algebraic-closure base change with `B`. The resulting inclusion is Borel both
   over `k` and after base change to the algebraic closure, as
   `IsGeometricBorelSubgroup` requires. Together with `hG` it gives
   `IsQuasiSplit G`.

The theorem adds no premises. In particular, it assumes no supplied Borel
subgroup, splitness, finite model or Frobenius invariance.

## Library inputs

- `Langlands.GroupScheme.Rational.FiniteFieldQuasiSplitStatement` — the target.
- `Langlands.GroupScheme.Rational.FrobeniusStableBorel` —
  `exists_frobeniusStableBorel_of_borelConjugacy`.
- `Langlands.GroupScheme.Absolute.FrobeniusBorelDescent` —
  `isQuasiSplit_of_borel_frobeniusTransport_eq`.
- `Langlands.GroupScheme.Absolute.BorelConjugacyProof` —
  `borelConjugacy : BorelConjugacyStatement.{u}`.
