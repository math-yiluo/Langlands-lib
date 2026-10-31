# Base change of actual geometric Weil-compatible level towers

Author: Worker 142.

This derived module supplies the geometric proofs to pointed and canonical
base change of the actual full and away compact-open Weil level towers.
It uses only the original base's torsion-order invertibility hypothesis.
Every declaration is in `Langlands.AbelianScheme.Tate.Geometric`.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18 / PDF p.26, defines the full and away
torsion inverse limits and their rationalizations over `ℤ`.
Section III.1, printed pp.91–92 / PDF pp.99–100, defines monodromy-invariant
orbits of pairing-compatible full and prime-to-p frames, canonical
geometric-point independence, level forgetting and right translation.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft built
2012-02-08, Chapter X, (10.25)–(10.26), printed p.150 / PDF p.154, defines
actual finite étale covers, the geometric-fibre functor and its
automorphism group. The latter is called the fundamental group on a
connected locally noetherian base. The discussion (10.29)–(10.30),
printed p.151 / PDF p.155, allows different algebraically closed endpoint
fields and describes the homomorphism induced by pullback of covers.
The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The new interfaces and formulas are internal specializations of
[GeometricWeilCompactOpenLevels](GeometricWeilCompactOpenLevels.md),
[WeilCompactOpenLevelBaseChange](WeilCompactOpenLevelBaseChange.md) and
[WeilCompactOpenLevelPathBaseChange](WeilCompactOpenLevelPathBaseChange.md).
They are not additional theorems quoted from these sources. The imported
maps use the actual torsion limits, Poincaré-derived Weil pairings,
twist actions, frame comparisons and geometric paths.

## Inputs and supplied geometry

Let `b : S' ⟶ S`, where both schemes are quasi-separated, and let
`A : AbelianScheme S`. Put `A_b = (baseChange b).obj A`.
The retained duality data are `HasDualScheme`, `DualSchemeGeometry`,
the line bundles `MA`, `MA'` and their displayed Poincaré evaluation
isomorphisms, on the two respective bases. The construction also retains
these named proposition inputs:

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement` and
  `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement` and
  `PicardZeroUniversalBaseChangeStatement`;
- `RelativeFiniteWeilTransitionStatement`.

The actual dual-valued map is
`lam : A ⟶ dualAbelianSchemeFromEvaluation ...`.
On the new base it is exactly
`canonicalDualValuedBaseChange b A ... lam`.
The actual rational algebra action
`i : D →ₐ[ℚ] Rationalization.End A` becomes
`(rationalBaseChangeEnd b A).comp i`.
The target map and action are therefore constructed from the source data.
The rational `D`-module `V`, its compatible scalar tower, and the rational
bilinear form `ψ` are common to both bases. No polarization predicate for
an arbitrary `lam` or extra PEL conditions are inferred from these data.

The full version uses
`h : Global.RationalProfiniteIntegerAdeleComparison` and
`hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))`.
The away version uses
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`
and units only at positive orders coprime to `m`. The modulus `m` is
natural; prime `m = p` recovers the prime-to-p version. General natural
moduli extend that source convention. The respective coefficient rings
are `Global.FiniteAdeles ℚ` and `Global.PrimeToFiniteAdeles m`.
Each coefficient comparison is shared between both bases and between
the Tate module and its actual twist.

For either selected family, the new-base unit witness is

```text
hunitb n = TateTwist.Geometry.InvertibleOrders.pullbackUnit b n.val (hunit n).
```

As proved in [TwistMonodromyUnits](TwistMonodromyUnits.md), this maps units
along the actual global-section homomorphism `b.appTop.hom`. There is no
independent new-base invertibility hypothesis. `selectedFinite` and
`selectedEtale` supply finite étaleness of each actual root kernel
`mu S n` and `mu S' n`, using `hunit` and `hunitb`, respectively.
The abelian torsion input is the published proof `torsionFiniteEtale`.
Every point is algebraically closed field-valued in universe `u`, so
`geometricFiberFinite` supplies finiteness at that point and its composite
with `b`. The geometric pairing transport theorem is already supplied by
the imported towers. None of these geometric proofs is a new hypothesis.

## Pointed pullback

Let `s : Spec Ω ⟶ S'` with `Ω` algebraically closed. Write `T_As` for
the geometric tower of `(A,lam,i)` at `s ≫ b`, and `T_bs` for that of
`(A_b,lam_b,i_b)` at `s`. Their common index category is respectively
`FiniteAdelicScalarExtensionLevel D V ψ` or
`PrimeToScalarExtensionLevel D V ψ m`.
An object at `K` is a right `K`-orbit of actual tensor-linear,
Weil-compatible frames fixed by the automorphism group of the actual
finite étale fibre functor. Pairing compatibility existentially quantifies
a linear trivialization of the actual Tate twist. A fixed orbit need
not contain a fixed frame.

`weilAdelicCompactOpenLevelBaseChange ... s` is a natural transformation
`P_s : T_As ⟶ T_bs`. It specializes the published pointed transformation
with all the proofs described above. Its `_app` formula identifies each
component with `Tate.weilAdelicLevelBaseChange ... K.toSubgroup`.
Its `_val` formula identifies the underlying orbit with
`(Tate.weilAdelicFrameRightOrbitBaseChange ... K.toSubgroup).symm q.val`.
The inverse is used because the existing frame comparison goes from the
base-changed fibre to the original fibre. Both formulas are reflexivity.

The theorem `_injective` specializes the published component-injectivity
theorem. The underlying orbit comparison is an equivalence, and the
actual fundamental-group homomorphism sends an old-base fixed orbit to
a new-base fixed orbit. No surjectivity of that homomorphism, or of the
map on fixed subsets, is required or asserted.

For every transporter arrow `f : K ⟶ L`, `_arrow` states

```text
P_s.app L (T_As.map f q) = T_bs.map f (P_s.app K q).
```

This is `NatTrans.naturality_apply` for the constructed transformation.
The tower arrow is the actual right translation `η ↦ η ∘ g`, with
`g⁻¹ K g ≤ L`. In particular the equation covers level forgetting.
With `[Module.Finite ℚ V]`, `_heckeLeft` and `_heckeRight` state this
same square for the two existing compact-open Hecke arrows from
`H = K ∩ g L g⁻¹` to `K` and `L`. The additional hypothesis supplies the
topological-group structure and compact open intersection used by those
arrows. Their proofs are also naturality.

## Canonical geometric-point pullback

Assume additionally that `S'` is connected and locally noetherian.
Let `t : Spec Ω' ⟶ S'` be another geometric point; the algebraically
closed fields `Ω` and `Ω'` may differ. Write `T_bt` for the new-base
tower at `t`.
`weilAdelicCompactOpenLevelGeometricBaseChange ... s t` constructs
`B_st : T_As ⟶ T_bt` by specializing the published canonical diagonal
transformation. The imported construction uses a path supplied by the
proved `geometricPathExists`.

The theorem `_GeometricBaseChange_eq_path` identifies `B_st` with
`Tate.weilAdelicCompactOpenLevelBaseChangeAlongPath ... p` for every
actual étale path
`p : fiberFunctor s (geometricFiberFinite s) ≅
     fiberFunctor t (geometricFiberFinite t)`.
This specializes the published path-independence theorem for entire
natural transformations. No path choice remains in the canonical map.

The theorem `_GeometricBaseChange_eq_transport` gives

```text
B_st = P_s ≫ GeometricTransport_b(s,t).hom,
```

using the geometric tower comparison from
`GeometricWeilCompactOpenLevels`. It is reflexivity after specializing the
same path-existence theorem and proofs. `_GeometricBaseChange_injective`
specializes the published diagonal injectivity result.
`_GeometricBaseChange_arrow` gives elementwise naturality for every
transporter, hence level forgetting and, under the finite-dimensional
hypothesis above, both Hecke legs.

For the final theorem also assume that `S` is connected and locally
noetherian. `_GeometricBaseChange_eq_pushed_transport` gives

```text
B_st = GeometricTransport_A(s ≫ b,t ≫ b).hom ≫ P_t.
```

This specializes the published base-change/path square and canonical
path-independence result with `geometricFiberFinite` at all four
endpoints. Together the two formulas identify the two routes around the
canonical point-comparison square.

Every construction and formula with prefix `weilAdelicCompactOpenLevel`
has its corresponding version with prefix
`weilPrimeToAdelicCompactOpenLevel`. The away proofs use exactly the
restricted-order geometric witnesses and pulled-back units above.

This unit constructs base-change transformations of the actual geometric
fixed-orbit towers under the displayed duality and coherence inputs.
Rank, frame nonemptiness, positivity, nondegeneracy, a polarization
predicate for `lam`, and construction or representability of the PEL
moduli functor remain outside its conclusions.
