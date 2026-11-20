# A spectral invariant along towers of base changes

Worker 5130 wrote this module for Task 7784. It defines an unramified invariant that
isobaric data over the levels of a tower `A ⊆ B ⊆ … ⊆ L` keep along weak base change. At
the top level it identifies the Satake parameters of the terminal datum. One universe `u`
holds all fields.

## Eigenvalue lemmas (namespace `Langlands.Unramified`)

- `Eigenvalues.coe_eq_of_eulerPolynomial_eq`: unramified parameters `a : Eigenvalues n`
  and `b : Eigenvalues m` with equal Euler polynomials have equal underlying multisets. The
  degree of the Euler polynomial gives `n = m`, and the published injectivity
  `Eigenvalues.eulerPolynomial_injective` does the rest.
- `Eigenvalues.coe_power`: the multiset of `a.power k` is that of `a` with every entry raised
  to the `k`-th power (by definition).
- `SpectralSystem.eigenvalues_congr`: the eigenvalues of a spectral system at equal places
  agree, whatever proofs of non-exceptionality are used.

## The invariant

Fix a number field `L`.

- `underPowerProfile s w`: for a spectral system `s` over a subfield `K` of `L` (an algebra
  `K → L`) and a finite place `w` of `L`. If `s` is defined at `w ∩ K` (the place
  `w.under (𝓞 K)`), it is the multiset of eigenvalues of `s` at `w ∩ K`, each raised to the
  power `f(w | w ∩ K)`, the inertia degree. Otherwise it is the empty multiset.
- `TowerSpectralInvariant A N D X`: for isobaric data `D` over a subfield `A` of `L`, a
  natural number `N`, and a profile `X : FinitePlace L → Multiset ℂˣ`. It says that
  `D.rank = N` and that some spectral system `s` is attached to `D`
  (`IsobaricData.HasSpectralSystem`) with the following property. For all but finitely
  many finite places `w` of `L`, if `s` is defined at `w ∩ A`, its eigenvalues there,
  each raised to `f(w | w ∩ A)`, form the multiset `X w`.

## Transfer lemmas

- `TowerSpectralInvariant.weakBaseChange`: for `A ⊆ B ⊆ L` (scalar tower) and `DB` a weak
  base change of `DA` (`IsobaricData.IsWeakBaseChangeOf`), the invariant passes from `DA` to
  `DB` with the same `N` and `X`. The new system is the one attached to `DB` in the weak
  base change relation. At almost every `w`, its eigenvalues at `w ∩ B` are those of the
  system of `DA` at `w ∩ A` raised to `f(w ∩ B | w ∩ A)`
  (`SpectralSystem.IsArithmeticWeakBaseChangeOf`). The system of `DA` in the relation and
  the one in the invariant agree almost everywhere, by the uniqueness of attached systems
  (`HasSpectralSystem.eventually_eigenvalues_eq`, in this task's
  `IsobaricSpectralUniqueness`). Then `f(w | w ∩ A) = f(w | w ∩ B) · f(w ∩ B | w ∩ A)`
  (`Ideal.inertiaDeg_tower`). `WeakInduction.tendsto_under_cofinite` (module
  `InductionBaseChangeHeckeFamily`) moves cofinite conditions from places of `A` or `B` to
  places of `L`.
- `TowerSpectralInvariant.arithmeticComap`: assume the cuspidal transport statement `hP`.
  For `e : A ≃+* A'` compatible with the embeddings into `L`, the invariant passes from `D`
  over `A'` to `D.arithmeticComap e` over `A`. The system comes from
  `IsobaricData.HasSpectralSystem.arithmeticComap` (module
  `IsobaricArithmeticSpectralTransport`). The places and inertia degrees match by
  `finitePlaceEquiv_under` and `inertiaDeg_eq_of_ringEquiv` (module
  `FinitePlaceEquivUnder`).
- `towerSpectralInvariant_ofCuspidal`: if `s` is attached to a cuspidal class `c` of rank
  `r + 1` over `K ⊆ L`, the one-constituent data of `c` satisfy the invariant with
  `N = r + 1` and profile `underPowerProfile s`.
- `TowerSpectralInvariant.eventually_coe_eigenvalues`: over `A = L` itself (algebra the
  identity), every inertia degree is `1` (`inertiaDeg_eq_one_of_finrank_eq_one`). So
  the invariant says that some system attached to `D` has eigenvalue multiset `X w` at almost
  every finite place `w` of `L` where it is defined.

## Provenance

Unramified base change of Satake parameters along an extension: the parameter at `w` is that
at `v = w ∩ A` raised to `f(w | v)` (Arthur–Clozel, Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula, Chapter III; as encoded in the Library's
`IsobaricData.IsWeakBaseChangeOf`). The invariant is internal to the project.
