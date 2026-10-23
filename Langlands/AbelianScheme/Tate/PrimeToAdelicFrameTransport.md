# Path-independent fixed orbits of actual prime-to-modulus adelic Tate frames

Author: Worker 142.

This module constructs frames in the actual rational Tate module away from a
modulus, the commuting right source action and left geometric monodromy action,
and transport on monodromy-fixed right orbits. It proves independence of a
supplied geometric path, identity, composition, reversal, and compatibility
with translating and forgetting level. Taking the modulus to be a prime gives
the prime-to-p version. These are ambient tensor-linear frames; a Weil-pairing
condition remains to be imposed.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), printed p.18 / PDF p.26 and Section III.1, printed pp.91–92 /
  PDF pp.99–100. Registered source
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  Page 18 defines the rational away Tate module by rationalizing the inverse
  limit over orders coprime to the omitted primes. Pages 91–92 describe the
  invariant full and prime-to-p right-orbit level data; page 91 gives the
  conjugate-subgroup condition for right translation.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X, (10.29), printed p.151 / PDF p.155. Registered source
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  This passage discusses noncanonical identification of fundamental groups at
  geometric points, including different algebraically closed point fields.

The cited original passages were read from local PDF text extractions. No
source-specific errata directory was available in the supplied Library.
The contribution is **derived**. It specializes the actual away scalar actions,
monodromy and geometric path maps in `AwayRationalScalars`, `RationalMonodromy`
and `RationalTransport`, using `LinearFrame` from `AdelicFrameTransport` and the
fixed-orbit operations in `OrbitTransport`. The arbitrary source representation,
the general modulus, and the omission of the pairing condition are internal
intermediate choices. The module does not claim to construct the full PEL
level structure in the sources.

## Actual carriers and explicit inputs

Fix an abelian scheme `A` over `S`, a natural number `m`, a rational algebra `D`,
and an algebra map `i : D →ₐ[ℚ] Rationalization.End A`. Retain the hypotheses

```lean
h : Global.RationalProfiniteIntegerAdeleComparison
hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m
```

The second comparison is coupled to the first. The same hypotheses and their
chosen comparison witnesses are used at all endpoints. Their truth and
independence of comparison witnesses are not proved here. In particular, the
full scalar-comparison hypothesis does not impose invertibility of all torsion
orders on the base scheme.

Set `R = D ⊗[ℚ] Global.PrimeToFiniteAdeles m`. The type
`PrimeToAdelicFrame A m hAway i V s` is

```text
V ≃ₗ[R] RationalAway A (Over.mk s) m.
```

Here `V` is an arbitrary `R`-module. The target is exactly
`ℚ ⊗[ℤ] Away A (Over.mk s) m`: its integral factor consists of compatible
actual torsion points with positive orders coprime to `m` and multiplication
transition maps. Its `R`-module instance is the constructed
`primeToFiniteAdeleAlgebraModule`, coming from actual rational endomorphisms
and the away finite-adelic action. It is not a tensor product over the integers
with the finite adeles. No rank, faithfulness, frame nonemptiness or topology
is assumed. The source group `G` and its representation
`ρ : G →* (V ≃ₗ[R] V)` are arbitrary.

The field-valued endpoints may have different fields in the same universe as
`S`. For monodromy and transport the hypotheses are

```lean
hs : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement
hu : ∀ n : GroupScheme.Tate.Index (fun n => Nat.Coprime n m),
  IsUnit (n.val : Γ(S, ⊤))
p : FiniteEtale.fiberFunctor s hs ≅ FiniteEtale.fiberFunctor t ht
```

Finite-fibre proofs are supplied at each endpoint. Only the retained orders
must be invertible on `S`; no prime assumption on `m` is used. For `m = p`
prime, the selected orders are precisely those prime to `p`. The intended
geometric application uses algebraically closed point fields and a connected,
locally noetherian base. This conditional API assumes only the displayed
inputs; existence of paths and the geometric finite-etaleness and
Galois-category theorems remain separate obligations.

## Actions and fixed quotient classes

`primeToAdelicFrameRightAction` applies `LinearFrame.rightAction ρ`, hence
`eta · g = eta ∘ ρ(g)` and `(eta · g) · k = eta · (g * k)`.
`primeToAdelicFrameMonodromyAction` applies `LinearFrame.leftAction` to
`primeToFiniteAdeleAlgebraMonodromyRepresentation`, the actual action of the
finite fibre-functor automorphism group on the away rational Tate module.
`primeToAdelicFrameActionsComm` proves these actions commute by the generic
precomposition/postcomposition calculation.

`PrimeToAdelicFrameOrbit ... U` is `InvariantOrbit` for these actions: it is
the subtype of right `U`-orbit classes fixed by every element of
`FundamentalGroup s hs`. It requires fixedness of the class, not a fixed
representative. `U` is any subgroup of `G`; a compact open subgroup can be
used through its underlying subgroup.

## Transport and its implemented proofs

`primeToAdelicFrameTransport p` postcomposes a frame with
`primeToFiniteAdeleAlgebraTransport ... p`. The application lemma identifies
this with the actual `rationalTransport` for the predicate
`fun n => Nat.Coprime n m`. The `_refl`, `_trans`, and `_symm` lemmas show
identity transport, `F_(p ≪≫ q) = F_q ∘ F_p`, and transport along the reverse
path as the inverse equivalence. Evaluation at each vector reduces these to
the existing rational Tate path laws.

`primeToAdelicFrameOrbitTransport U p` applies `InvariantOrbit.equiv` to this
frame equivalence and `pathConjugation p`. Right equivariance is composition;
left equivariance is `rationalTransport_monodromy` at every vector. For two
paths `p` and `q`, the actual `rationalTransport_change_path` formula gives

```text
F_q(eta) = (p.symm ≪≫ q) • F_p(eta).
```

The automorphism on the right lies in the target fundamental group.
`primeToAdelicFrameOrbitTransport_path_independent` uses
`InvariantOrbit.equiv_eq_of_left` to cancel its action on a fixed orbit. It
proves equality of the whole orbit equivalences for any supplied paths with
the same endpoints. It does not identify the representative frame transports
or the induced group isomorphisms, and it does not prove that paths exist.
The orbit `_refl`, `_trans`, and `_symm` lemmas use equivalence and subtype
extensionality followed by quotient induction and the corresponding frame
laws. Thus the path-independent orbit equivalences compose coherently.

## Level changes and remaining scope

`primeToAdelicFrameOrbitTranslate g hg` sends `U`-orbits to `U'`-orbits by
`eta ↦ eta ∘ ρ(g)` under `hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U'`.
`primeToAdelicFrameOrbitForget` specializes to `g = 1` and `U ≤ U'`.
The transport `_translate` lemma applies `InvariantOrbit.map_translate`, with
the same actual monodromy-equivariance proof, to show that path transport
commutes with right translation. The `_forget` square is its specialization.

Weil pairings, Tate twists, polarization compatibility, and the resulting
similitude-frame subtype remain separate. This construction does not choose
roots of unity or trivialize twist monodromy. Rational/adelic continuity,
pointed base change, path existence and the canonical unpointed PEL functor
are not constructed here. No map from full frame spaces to away frame spaces
is asserted: such a map requires the corresponding source scalar extension
and its compatibility with the actual Tate restriction. Parent-task completion
is not claimed.
