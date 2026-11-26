# Weak base change of isobaric data in a tower: proof

Module: `Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeTowerProof`.

`Langlands.Automorphic.Unramified.isobaricWeakBaseChangeTower` proves the published
proposition
`Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeTowerStatement.{uF, uK, uE, uV, uM, uW}`
of [IsobaricWeakBaseChangeTransportStatement](IsobaricWeakBaseChangeTransportStatement.md),
with all six universe parameters and no added hypothesis. For number fields `F ⊆ K ⊆ E`
(with `IsScalarTower F K E` and compact adele quotients), if `DK` is a weak base change of
`DF` (`IsobaricData.IsWeakBaseChangeOf.{uF, uK, uV, uM}`) and `DE` is a weak base change of
`DK` (`IsobaricData.IsWeakBaseChangeOf.{uK, uE, uM, uW}`), then `DE` is a weak base change
of `DF` (`IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}`). No Galois, cyclicity or degree
hypothesis is made on the tower.

## Source

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), Chapter III. Weak base change is Definition 1.1 with the identity (1.1)
`t_{Π,w} = t_{π,v}^{f_v}` at almost all places, printed p. 199 (PDF p. 213). In §6 the
composite cyclic degree is reduced to prime degree through towers of cyclic extensions: the
proof of Theorem 6.2 (stated on printed p. 215) runs to printed p. 217, and the proof of
Lemma 6.3, printed p. 217 (PDF p. 231), passes through an intermediate field
`E ⊇ E₁ ⊇ F` and concludes "by transitivity of the lifting identities (1.1)". The registered
source is `arthur-clozel-1989-base-change` with SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`. The Lean proof below
carries out this transitivity for the numerical relation
`SpectralSystem.IsArithmeticWeakBaseChangeOf`, which also requires every place above a tested
base place to be unramified.

## The implemented proof

The module proves two lemmas on spectral systems, in namespace
`Langlands.Unramified.SpectralSystem`, and then the theorem.

### `IsArithmeticWeakBaseChangeOf.trans_of_eventually_eigenvalues_eq`

Let `s` be a spectral system over `F`, `t` and `t'` systems over `K` and `u` a system over
`E`, all of rank `n`. Assume `t` is an arithmetic weak base change of `s`, `u` one of `t'`,
and `t` and `t'` have equal spectra at almost all finite places of `K` where both are defined.
Then `u` is an arithmetic weak base change of `s`.

1. The places `w` of `K` where either the middle comparison or the defining condition of
   `u` over `t'` fails form a finite set (`Filter.eventually_cofinite`).
2. By `eventually_avoidsAbove` (module `Langlands.Representation.Unramified.WeakTransfer`),
   for almost all places `v` of `F` no place of `K` above `v` lies in that finite set: the
   contraction to `F` of the omitted primes is finite. The proof intersects this with the
   cofinite set of places `v` where the condition of `t` over `s` holds.
3. Fix such a `v` and a place `x` of `E` above `v`. Its contraction
   `w = x.under (𝓞 K)` is a place of `K`; `x` lies over `w` (`liesOver_under`) and `w`
   lies over `v` (`Ideal.LiesOver.tower_bot`). Hence `w` is a place above `v` outside the
   finite set, so `t'` is defined at `w`, `u` is defined at `x`, `x` is unramified over `w`
   and the spectrum of `u` at `x` is that of `t'` at `w` raised to the residue degree of `x`
   over `w`.
4. Ramification: `Ideal.ramificationIdx_tower` writes the ramification index of `x` over `F`
   as the index of `w` over `F` times that of `x` over `K`; both are `1`.
5. Spectra: the spectrum of `t'` at `w` is that of `t` at `w` by the middle comparison, which
   is the spectrum of `s` at `v` raised to the residue degree `f(w/v)`. Then
   `Eigenvalues.power_power` combines the two powers into the exponent
   `f(w/v) · f(x/w)`, which is `f(x/v)` by `Ideal.inertiaDeg_tower`.

### `IsArithmeticWeakBaseChangeOf.trans_eqRec`

`IsobaricData.IsWeakBaseChangeOf` compares the rank cast `h ▸ t` of the upper system with the
lower system. This lemma states the composition for ranks related by `m = n` and `p = m`,
with the casts `hmn ▸ t`, `hpm ▸ u` and `(hpm.trans hmn) ▸ u`. Substituting both equalities
reduces it to the previous lemma.

### `isobaricWeakBaseChangeTower`

From the two hypotheses the proof takes the rank equalities `DK.rank = DF.rank` and
`DE.rank = DK.rank`, a system `s` attached to `DF` and a system `t` attached to `DK` (local
factors in universes `uV` and `uM`) with `t` a weak base change of `s`, and a system `t'`
attached to `DK` and a system `u` attached to `DE` (universes `uM` and `uW`) with `u` a weak
base change of `t'`. The two middle systems come from possibly different enumerations of the
multiset `DK` and different presentations of its constituents.
`IsobaricData.HasSpectralSystem.eventually_eigenvalues_eq` (module
`Langlands.Automorphic.Unramified.IsobaricSpectralUniqueness`) shows that `t` and `t'` have
equal spectra at almost all places of `K`: it matches the constituents of the two
enumerations with multiplicities through the multiset `DK`, and compares two presentations of
one cuspidal class by `CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq` (module
`Langlands.Automorphic.AssociatedPresentationSpectrum`). The witness for `DE` over `DF` is
then the rank equality `DE.rank = DF.rank`, the system `s` with its attachment to `DF`, the
system `u` with its attachment to `DE`, and the relation given by `trans_eqRec`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
