# Actual prime-adic Tate transport along geometric paths

Author: Worker 142.

This module constructs transport on the existing integral and rational
prime-adic Tate modules along a supplied isomorphism of actual finite fibre
functors. Integral transport is a continuous linear equivalence; rational
transport is an algebraic linear equivalence. The module proves the path
laws, compatibility with actual monodromy and homomorphisms, and the selected,
full and away prime-coordinate comparison squares.

## Sources and derived provenance

- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft built
  2012-02-08, Chapter X, (10.2)–(10.3), printed p.142 / PDF p.146;
  (10.5), printed p.143 / PDF p.147; Definitions (10.25)–(10.26),
  printed p.150 / PDF p.154; and (10.29), printed p.151 / PDF p.155.
  Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
  SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  Pages 142–143 give the prime-power limit, its coordinatewise prime-adic
  scalars, rationalization and functoriality. Pages 150–151 define the
  finite étale fibre functor, its automorphism group and noncanonical
  change of geometric base point.
- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26. Registered source:
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  This page defines the full and away torsion limits and their rationalizations.

These original passages were read. No source-specific errata file was found
in the available Library. This construction is **derived** from the existing
finite-level path transport, prime-adic limits and scalar extensions.
Coordinate extensionality transfers the finite path laws; tensor induction
transfers them to rational modules. Prime-coordinate compatibility follows
from the existing extraction maps. The conditional selected-index API is
internal infrastructure, not a claim that these exact declarations occur
in either source.

## Actual objects and hypotheses

The transport declarations lie in `Langlands.AbelianScheme.Tate.PrimeAdic`.
Fix an actual `A : AbelianScheme S`, a prime `p : ℕ` with `[Fact p.Prime]`,
fields `Ω`, `Ω'`, and points `s : Spec (.of Ω) ⟶ S`,
`t : Spec (.of Ω') ⟶ S`. The fields and base scheme share the universe `u`,
but the fields need not be equal. The assumptions are

```lean
hs : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
ht : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber t Y)
htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement
hu : ∀ n : ℕ, IsUnit ((p ^ n : ℕ) : Γ(S, ⊤))
e : FiniteEtale.fiberFunctor s hs ≅ FiniteEtale.fiberFunctor t ht
```

The existing `primePower_isUnit` derives `hu` from invertibility of `p` in
the global sections. The hypothesis `htor` supplies finite étaleness of the
actual multiplication kernels at these invertible orders. The path `e` is
a natural isomorphism on actual finite étale covers, not a supplied map
between Tate modules.

The intended geometric setting uses algebraically closed fields and a
connected locally noetherian base. The conditional construction here uses
only the displayed data and does not prove existence of `e`, finite fibres,
finite étaleness, or a Galois-category classification.

The integral carrier is `PrimeAdic.Integral A (Over.mk s) p`, the existing
coherent sequence of actual `A[p^n]` sections with successive multiplication
by `p` transitions. It retains the existing coordinatewise `ℤ_[p]` action
and the subspace topology from the product of discrete torsion levels.
The rational carrier is the existing
`ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral A (Over.mk s) p`.
No basis or replacement module is introduced.

## Integral transport and its laws

`levelTransportLinear` uses actual `levelTransport` at order `p^n`.
Its scalar law applies the finite `ZMod (p^n)` transport law to
`PadicInt.toZModPow n a`. `transportMap` uses the prime-adic universal
`lift` to apply this linear map at every coordinate. Its coherence proof
uses `levelTransport_transition` and the input sequence's coherence.
`evaluation_transportMap` gives the defining formula

```text
(T_p(e)x)_n = T_{p^n}(e)(x_n).
```

`transportMap_refl` and `transportMap_trans` reduce to the finite-level
laws by subtype and coordinate extensionality. For `e : s → t` and
`f : t → r`, where these arrows denote fibre-functor paths, the order is

```text
T_p(e followed by f)(x) = T_p(f)(T_p(e)(x)).
```

`transport` bundles this map as a `ℤ_[p]`-linear equivalence with inverse
`transportMap` for `e.symm`. The inverse proofs use composition and identity.
`transport_apply`, `transport_refl`, `transport_trans`, and
`transport_symm` expose these facts for the equivalence.
`transport_aut` identifies loop transport with the existing
`PrimeAdic.monodromy` by definitional equality.

`continuous_transport` uses product and subtype continuity. Each output
coordinate is `continuous_levelTransport` composed with the existing
continuous evaluation. `transportContinuousLinearEquiv` bundles the
linear equivalence and this continuity result in both directions, using
the reverse path for inverse continuity. The topology remains the existing
one on the actual prime-adic limit.

`transport_monodromy` intertwines source monodromy with target monodromy
through `pathConjugation e`. This conjugation has underlying function
`e ∘ g ∘ e⁻¹`. For two paths `e,f : s → t`,
`transport_change_path` states

```text
T_p(f)(x) = ρ_t(e.symm followed by f)(T_p(e)(x)).
```

The target loop has underlying function `f ∘ e⁻¹`. Both laws reduce
coordinatewise to the finite transport equations. They describe dependence
on the chosen path; they do not assert equality of arbitrary path maps.
For an actual abelian-scheme homomorphism `a : A ⟶ B`,
`transport_map` proves the naturality square for the existing induced maps
at `s` and `t`. Its proof reduces to `levelTransport_map`.

## Rational extension

`rationalTransportMap` is `transportMap.baseChange ℚ_[p]`. Its
`rationalTransportMap_tmul` formula is

```text
T_{V_p}(e)(a ⊗ x) = a ⊗ T_p(e)(x).
```

Tensor induction proves `rationalTransportMap_refl` and
`rationalTransportMap_trans`. `rationalTransport` retains this forward
map and uses the reverse-path map as inverse; the inverse proofs use
these two laws. The lemmas `rationalTransport_apply`,
`rationalTransport_tmul`, `rationalTransport_refl`,
`rationalTransport_trans`, and `rationalTransport_symm` record the
resulting maps and path laws. `rationalTransport_aut` identifies its
loop case with the existing rational prime-adic monodromy.

`toRational_transport` proves compatibility with the map `x ↦ 1 ⊗ x`,
without asserting injectivity. The equations
`rationalTransport_monodromy`, `rationalTransport_change_path`, and
`rationalTransport_map` extend the integral conjugation, change-of-path
and actual-homomorphism laws by tensor induction. This part is algebraic:
no rational topology or continuity theorem is introduced.

## Prime-coordinate squares

The comparison declarations lie in
`Langlands.AbelianScheme.Tate.PrimeComparison`. Fix a selected predicate
`P : ℕ → Prop` with

```lean
hu : ∀ n : GroupScheme.Tate.Index P, IsUnit (n.val : Γ(S, ⊤))
hP : ∀ n : ℕ, P (p ^ n)
```

The prime-adic transport uses exactly
`fun n => hu (primePowerIndex P p hP n)`.
`toPrime_transport` proves that prime extraction after integral selected
transport equals prime-adic transport after prime extraction.
Both sides read the same coordinate and apply the same finite path map,
so this equality is definitional.
`toPrimeContinuousSemilinear_transport` gives the identical square for
the existing continuous semilinear extraction over
`Global.ProfiniteIntegerRing.toPadic p`.

`rationalToPrime_transport` gives the rational square for the existing
map between different scalar extensions:

```text
Q ⊗_Z T_P  →  Q_p ⊗_{Z_p} T_p,
q ⊗ x      ↦  (q : Q_p) ⊗ toPrime(x).
```

Its proof uses tensor induction and the integral coordinate equality.
`rationalToPrimeSemilinear_transport` states the same square for the
existing semilinear bundle over
`Global.ProfiniteIntegerRing.rationalToPadic p`.

The full versions are `fullToPrimeContinuousSemilinear_transport`,
`rationalFullToPrime_transport`, and
`rationalFullToPrimeSemilinear_transport`. They use `P n = True`.
The away versions are `awayToPrimeContinuousSemilinear_transport`,
`rationalAwayToPrime_transport`, and
`rationalAwayToPrimeSemilinear_transport`. They use
`P n = Nat.Coprime n m` and require `hp : Nat.Coprime p m`;
`hp.pow_left n` retains every prime power. For positive `m` these are
exactly the primes not dividing `m`. The case `m = 1` retains all primes;
no prime satisfies the away hypothesis for `m = 0`.

All scalar and continuity structures of these extraction maps are
imported unchanged. The squares assert compatibility of the constructed
path maps with those actual extraction maps; they do not assume or prove
a prime-product or restricted-product identification.

## Remaining scope

Path existence, the geometric hypotheses, pointed base change, pairings,
and independence of invariant level orbits remain separate obligations.
This unit does not construct prime-adic Hom⁰/End⁰ actions, rational
continuity, or an absolute-Galois-group comparison. It extends the
already constructed actual monodromy to paths between points and proves
the stated compatibility laws without completing the parent PEL task.
