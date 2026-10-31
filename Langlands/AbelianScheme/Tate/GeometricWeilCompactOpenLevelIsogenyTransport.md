# Rational isogenies between geometric-point Weil level towers

Author: Worker 142.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Section III.1, printed p.91 / PDF p.99, defines level
structures as invariant orbits of compatible adelic frames, uses
isogenies respecting the rational algebra action and polarization up
to a nonzero rational multiple, and asserts canonical independence
from the geometric point. It also gives level forgetting and right
translation. Printed p.92 / PDF p.100 gives the prime-to-p compatible
frame variant. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft
built 2012-02-08, Chapter X, (10.25)–(10.26), printed p.150 / PDF
p.154, defines actual finite étale covers, the geometric-fibre functor
and its automorphism group. Section (10.29), printed p.151 / PDF
p.155, discusses comparison of geometric points whose algebraically
closed fields may differ. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This is a derived assembly of
[GeometricWeilCompactOpenLevelIsogeny](GeometricWeilCompactOpenLevelIsogeny.md),
[GeometricWeilCompactOpenLevels](GeometricWeilCompactOpenLevels.md),
[WeilCompactOpenLevelTransport](WeilCompactOpenLevelTransport.md)
and the fixed-level square in
[WeilLevelIsogeny](WeilLevelIsogeny.md).
The new construction compares the tower of one actual abelian scheme
at one geometric point with the tower of another at a different
point. Its commuting squares and coherence laws are deductions from
these Library implementations, rather than separate theorems quoted
from the literature. All declarations are in
`Langlands.AbelianScheme.Tate.Geometric`.

## Actual data and retained hypotheses

The base `S : Scheme.{u}` is quasi-separated. The endpoints `A` and
`B` are actual abelian schemes over `S`. For each endpoint the
interface retains `HasDualScheme`, `DualSchemeGeometry`, an inverse
Poincaré line bundle, its displayed tensor evaluation isomorphism,
and a homomorphism `lam` into the resulting constructed dual abelian
scheme. These are general dual-valued homomorphisms; this interface
does not certify them as polarizations.

The retained proposition inputs are
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, `PicardZeroPullbackStatement`,
`DualSchemeMapAdditivity` for the ordered pair `A,B`, and
`RelativeFiniteWeilTransitionStatement`. The implemented pairing
functoriality and pairing transport use the proved
`rationalWeilFunctoriality` and `rationalWeilGeometricTransport`.

The rational algebra `D` has actual actions
`iA : D →ₐ[ℚ] Rationalization.End A` and similarly for `B`.
The module `V : Type w` has compatible rational and `D`-module
structures, and `ψ` is a rational bilinear form. No finite-dimensionality,
faithfulness, alternation or nondegeneracy is inferred from these
inputs. The full PEL conditions are stated separately by
`RationalPELConditions`.

The points `s : Spec Ω ⟶ S` and `t : Spec Ω' ⟶ S` have
algebraically closed fields in universe `u`; the fields may differ.
For the full version, retain
`h : Global.RationalProfiniteIntegerAdeleComparison` and units in
`Γ(S, ⊤)` at all positive orders. For the away version, retain
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`
and units only at positive orders coprime to the natural modulus
`m`. The coefficients are respectively `Global.FiniteAdeles ℚ` and
`Global.PrimeToFiniteAdeles m`. At prime modulus `m = p` this is the
prime-to-p version used by the source; arbitrary natural moduli extend
that application. The ambient comparison `h` in the away interface
does not impose full-order unit hypotheses.

As in the imported geometric constructions, `geometricFiberFinite`
supplies finiteness of every actual finite étale cover's geometric
fibre, `torsionFiniteEtale` supplies finite étaleness of the abelian
torsion kernels at the selected invertible orders, and
`TateTwist.Geometry.InvertibleOrders.selectedFinite` and
`selectedEtale` supply finite étaleness of the selected roots-of-unity
schemes. None is an extra finiteness hypothesis of this interface.
The acting group at `s` is precisely
`FundamentalGroup s (geometricFiberFinite s)`.

Write `T_A(s)` and `T_B(t)` for the imported geometric compact-open
level towers. At a compact open subgroup `K`, their values are the
monodromy-fixed right `K`-orbits of actual compatible frames.
Compatibility uses the actual Poincaré-derived Weil pairing pulled
back along `lam` and an existential scalar-linear trivialization of
the actual adelic Tate twist. No roots of unity or twist
trivialization are chosen in the level definition. Fixedness is a
property of the orbit, without requiring a fixed frame representative.

## Supplied-path comparison and its square

Let `q : ℚˣ` and let
`e : Rationalization.of A ≅ Rationalization.of B` be an actual
invertible rational homomorphism. Retain the equation `he` that its
forward map intertwines the two rational algebra actions and the
actual dual pullback identity `hqe`, expressed by
`IsRationalDualPullbackMultiple`:

`e^∨ ∘ lamB ∘ e = q · lamA`

in rationalized Hom. This is an identity for the constructed dual
homomorphism and the given `lam` maps, not an arbitrary condition on
output bilinear forms. Let `I_e(s)` denote the imported fixed-point
natural isomorphism. Its components descend postcomposition by the
actual rational Tate map induced by `e.hom`.

For an actual fibre-functor path

`p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t)`,

write `P_A(p)` and `P_B(p)` for the published natural path
isomorphisms. The definition `weilAdelicCompactOpenLevelIsogenyPath`
is

`M_e(p) = I_e(s) ≪≫ P_B(p) : T_A(s) ≅ T_B(t)`.

The theorem with suffix `_eq_transport_isogeny` proves

`M_e(p) = P_A(p) ≪≫ I_e(t)`.

Its proof applies `Iso.ext`, extensionality at a compact-open index
and element, then the published `weilAdelicLevelIsogeny_transport`
square with the geometric witnesses supplied. That square ultimately
uses naturality of the actual rational Tate map with respect to the
fibre-functor path. Thus both orders use the same given isogeny and
the same actual path; no commuting-square hypothesis is added.

The theorem `weilAdelicCompactOpenLevelIsogenyPath_independent`
proves equality for any two such paths `p,p'`. It unfolds the new
definition and uses the published path independence of `P_B` on
fixed-orbit towers. These supplied-path constructions do not require
connectedness or local noetherianity of `S` beyond the displayed
quasi-separatedness and the existence of the supplied paths.

## Canonical comparison between geometric points

For this part assume additionally that `S` is connected and locally
noetherian. The published theorem `geometricPathExists` gives an
actual fibre-functor path between the two geometric points, and the
published point-comparison construction removes its choice on
fixed-orbit towers. Write `C_A(s,t)` and `C_B(s,t)` for those canonical
point comparisons.

The definition `weilAdelicCompactOpenLevelGeometricIsogeny` is

`J_e(s,t) = I_e(s) ≪≫ C_B(s,t) : T_A(s) ≅ T_B(t)`.

The following laws are implemented:

- `_eq_path` identifies `J_e(s,t)` with `M_e(p)` for every actual
  supplied path. The proof rewrites `C_B(s,t)` by the published
  canonical-comparison theorem for that path.
- `_eq_transport_isogeny` proves
  `J_e(s,t) = C_A(s,t) ≪≫ I_e(t)`. The proof chooses one path using
  `geometricPathExists`, rewrites both canonical comparisons to it,
  and invokes the already proved supplied-path square.
- `_hom_app` and `_inv_app` expose the forward component as first
  `I_e(s)` then `C_B(s,t)`, and the inverse component in the reverse
  order. Both are reflexivity proofs for composition of natural
  isomorphisms. The imported isogeny and transport component formulas
  further identify these maps with their actual fixed-level
  equivalences.
- `_samePoint` proves `J_e(s,s) = I_e(s)`, by the published identity
  law for canonical point transport and the right identity law for
  composition of isomorphisms.

For a third geometric point `r : Spec Ω'' ⟶ S`, with an
algebraically closed field in universe `u`, the theorem
`_target_trans` proves

`J_e(s,r) = J_e(s,t) ≪≫ C_B(t,r)`.

It unfolds the definition, uses transitivity of `C_B`, and reassociates
isomorphism composition. The theorem `_source_trans` proves

`J_e(s,r) = C_A(s,t) ≪≫ J_e(t,r)`.

It combines `_target_trans`, the mixed square and associativity.
These laws preserve the same `e`, `q`, `he` and `hqe`; they add no
new multiplier identity or point-comparison hypothesis. The
canonicality asserted here is for the resulting fixed-orbit tower
isomorphism, without asserting a canonical fibre-functor path or a
canonical isomorphism of fundamental groups.

## Transporters, Hecke legs and the away version

The theorem `_arrow` is naturality for every transporter arrow
`f : K ⟶ L`:

`J_e(s,t)_L (T_A(s)(f)(x)) = T_B(t)(f)(J_e(s,t)_K(x))`.

The transporter convention is the published right action by frame
precomposition; its condition is `g⁻¹ K g ≤ L`. Level forgetting is
the inclusion arrow with element `1`. Thus this equality includes
level forgetting with its correct direction.

In the Hecke section only, assume `[Module.Finite ℚ V]`, as required
by the published compact-open Hecke-level construction. For compact
open `K,L` and an actual similitude point `g`, the intermediate level
is `K ∩ g L g⁻¹`. The theorems `_heckeLeft` and `_heckeRight` are the
same naturality square for the actual inclusion leg to `K` and the
translation leg to `L`. Each proof is the constructed natural
transformation's `naturality_apply`.

Every definition and theorem above has the corresponding
`weilPrimeToAdelic...` declaration in the second section, including
the supplied-path square and independence, canonical comparison and
every-path formula, component formulas, equal-point recovery, both
third-point laws, transporter naturality and both Hecke squares.
The proofs use the corresponding away fixed-level square and path
comparison with the coprime-order geometric witnesses. They retain
only coprime-order unit hypotheses and use the same coupled
coefficient comparison for the Tate module and its actual twist.

This unit proves comparison of these towers at one fixed base under
the retained explicit construction hypotheses. It does not prove a
new mixed base-change/isogeny law, certify the general `lam` maps as
polarizations, establish rank, nondegeneracy, positivity or frame
nonemptiness, or construct a PEL moduli functor or its representability.
