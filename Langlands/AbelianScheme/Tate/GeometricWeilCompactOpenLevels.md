# Actual geometric Weil-compatible compact-open level towers

Author: Worker 142.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18, defines the full and away torsion limits
and their rationalizations over `ℤ`. Section III.1, printed p.91, defines
levels by monodromy-invariant orbits of pairing-compatible adelic frames,
describes level forgetting and right translation, and states canonical
geometric-point independence. Printed p.92 gives the prime-to-p variant.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`;
the corresponding PDF pages are 26 and 99–100.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft
built 2012-02-08, Chapter X, Definitions (10.25)–(10.26), printed p.150 /
PDF p.154, defines finite étale covers, the actual geometric-fibre
functor and its automorphism group. Its fundamental-group terminology
uses a connected locally noetherian base. This source is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This module is a derived specialization of
[WeilCompactOpenLevels](WeilCompactOpenLevels.md) and
[WeilCompactOpenLevelTransport](WeilCompactOpenLevelTransport.md).
It supplies their geometric-fibre finiteness, abelian torsion finite
étaleness and selected roots-of-unity finite étaleness from published
proofs. The tower, frame spaces, pairings, actions and path comparisons
are those already constructed in the Library. The new interface and
its application formulas are internal deductions, rather than
verbatim statements of the cited literature.

## Inputs and geometric proofs

Let `S : Scheme.{u}` be quasi-separated and `A : AbelianScheme S`.
The explicit duality inputs are `HasDualScheme A`, `DualSchemeGeometry`,
the line bundle `MA`, its displayed evaluation isomorphism against the
Poincaré family, and an actual homomorphism
`polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation ...`.
The name of this map does not certify that it is a polarization.
The construction retains the following named proposition inputs:

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement` and
  `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`;
- `RelativeFiniteWeilTransitionStatement`.

Let `D` be a rational algebra, with an actual action
`i : D →ₐ[ℚ] Rationalization.End A`. Let `V : Type w` be an additive
group with compatible rational and `D`-module structures, and let `ψ`
be a rational bilinear form on `V`. This interface accepts these data
without imposing the extra PEL conditions. The intended finite
dimensionality, faithfulness, involution compatibility, alternation and
nondegeneracy conditions are expressed separately by
`RationalPELConditions`.

Every point `s : Spec Ω ⟶ S` in this module has an algebraically closed
field `Ω : Type u`. The finite-fibre witness is the published proof
`geometricFiberFinite s`. The abelian torsion witness is
`torsionFiniteEtale`, used with the retained invertibility hypothesis
for each selected positive order. The roots-of-unity witnesses are
`TateTwist.Geometry.InvertibleOrders.selectedFinite` and
`selectedEtale`, applied to that same invertibility hypothesis. As
explained in [TwistMonodromyUnits](TwistMonodromyUnits.md), these follow
from the published finite étaleness of the actual group scheme `mu S n`.
The underlying torsion kernels and roots-of-unity schemes are unchanged.

The full construction uses all positive orders, an input
`h : Global.RationalProfiniteIntegerAdeleComparison`, and
`hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))`.
Its coefficient ring is `Global.FiniteAdeles ℚ`.
The away construction uses orders coprime to a natural modulus `m`,
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`,
and units only at those positive orders. Its coefficient ring is
`Global.PrimeToFiniteAdeles m`. The ambient `h` in this comparison
concerns coefficient rings; the away construction requires no
full-order unit hypothesis. A prime modulus gives the prime-to-that-prime
version in Harris–Taylor. General natural moduli are an extension of
that interface.

The pairing transport input is supplied by the published theorem
`rationalWeilGeometricTransport`, already installed by the imported
tower. Thus neither geometric pairing transport nor any of the three
finite-étale witnesses is an additional hypothesis of the new towers.
The named duality, coherence and finite Weil transition dependencies
above remain explicit.

## The actual fixed-orbit towers

All new declarations lie in
`Langlands.AbelianScheme.Tate.Geometric`. Write `R` for the full or
away coefficient ring. The source similitude group is
`ScalarExtensionSimilitudePoints D V R ψ`, acting on `R ⊗[ℚ] V`.
The existing tensor-commutativity comparison relates this source
convention to the source's `V ⊗[ℚ] R`.

At `s`, a frame is the existing actual `D ⊗[ℚ] R`-linear isomorphism
from this scalar extension to the rationalized torsion inverse limit
of `A`. The latter is `ℚ ⊗[ℤ] T`, with `T` the actual full or away
torsion-section limit, equipped with the published adelic action.
Pairing compatibility existentially quantifies an `R`-linear
trivialization of the actual rational Tate twist identifying the
standard form with the Poincaré-derived pairing pulled back along
`polarizationMap` in the second variable. Such a trivialization is
not chosen as frame data. The actual geometric action acts on both
the Tate module and the twist.

`weilAdelicCompactOpenLevelTower ... s` has type
`FiniteAdelicScalarExtensionLevel D V ψ ⥤ Type (max u w)`.
`weilPrimeToAdelicCompactOpenLevelTower ... s` uses
`PrimeToScalarExtensionLevel D V ψ m`. Each index `K` is an actual
compact open subgroup of the indicated source similitude group.
The object at `K` is the set of right `K`-orbits of these actual
Weil-compatible frames fixed by
`FundamentalGroup s (geometricFiberFinite s)`, the automorphism group
of the actual finite-étale geometric-fibre functor. Fixedness belongs
to the orbit and requires no fixed representative.

`WeilAdelicCompactOpenLevel` and
`WeilPrimeToAdelicCompactOpenLevel` abbreviate these tower objects.
The respective `_obj` formulas identify them with the existing
compact-open level sets after supplying the geometric proofs.
An arrow `f : K ⟶ L` has an actual group element `g` satisfying
`g⁻¹ K g ≤ L`. The `_map` formulas identify its action with
the published fixed-orbit translation, which sends the class of `η`
to the class of `η ∘ g`. The `_inclusion` formulas identify
the arrow associated to `K ≤ L` with the published forgetting map.
These formulas are proved by reflexivity. The inherited functor laws
give identity and the right-action composition order: first `g`,
then `k`, acts by `g * k`.

With the additional assumption `Module.Finite ℚ V`, the source
similitudes have the topological-group structure needed for the
compact open intersection `H = K ∩ g L g⁻¹`.
`weilAdelicCompactOpenHeckeLeft` and
`weilAdelicCompactOpenHeckeRight` are the tower maps from `H` to
`K` and `L`. The first uses the inclusion arrow, and the second
uses the transporter arrow with element `g`. The away Hecke
definitions have the same meaning. They reuse the existing
`CompactOpenLevel.heckeLeft`, `heckeRight` and `heckeLevel`.

## Canonical geometric-point comparisons

For this part additionally assume `[ConnectedSpace S]` and
`[IsLocallyNoetherian S]`. The algebraically closed endpoint fields
may be different fields in universe `u`.
`weilAdelicCompactOpenLevelGeometricTransport ... s t` is a natural
isomorphism of the full towers at `s` and `t`.
`weilPrimeToAdelicCompactOpenLevelGeometricTransport` is the away
version. Both specialize the published canonical tower comparison,
with all finite-fibre and finite-étale witnesses supplied as above.

The imported comparison chooses an actual étale path whose existence
is proved by `geometricPathExists`, and the imported fixed-orbit
path-independence theorem removes that choice. The new `_eq_path`
theorems identify the canonical comparison with the existing tower
transport along every supplied
`p : fiberFunctor s (geometricFiberFinite s) ≅
     fiberFunctor t (geometricFiberFinite t)`.
The `_refl` and `_trans` theorems assert identity at one point and
transitivity through a third point, respectively. Their proofs
specialize the corresponding published tower theorems.

The `_arrow` theorems state the elementwise naturality square for
every transporter arrow. They follow by
`NatTrans.naturality_apply` for the constructed natural isomorphism.
They therefore include compatibility with level forgetting and,
under the stated finite-dimensional hypothesis, both Hecke legs.
No path is supplied in the canonical comparison or in these
naturality, identity and transitivity statements.

This unit constructs actual geometric fixed-orbit towers with
canonical point comparisons while retaining the stated duality
dependencies. It asserts no rank, chosen basis, nonempty frame
space, positivity or nondegeneracy of the supplied dual-valued map.
It does not construct a topology on the frame or level set, a
comparison between different abelian schemes, pointed base-change
maps, or the PEL moduli functor itself.
