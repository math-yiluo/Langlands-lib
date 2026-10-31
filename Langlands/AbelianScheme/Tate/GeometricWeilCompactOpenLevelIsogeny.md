# Rational isogenies of actual geometric Weil-compatible level towers

Author: Worker 142.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18 / PDF p.26, defines an isogeny of abelian
schemes as an invertible element of rationalized Hom, and defines the
full and away Tate modules and their rationalizations. Section III.1,
printed p.91 / PDF p.99, uses isogenies respecting the rational algebra
action and polarization up to a nonzero rational multiple to compare
quadruples with monodromy-invariant orbits of compatible frames. The
same page describes level forgetting and the right adelic action.
Printed p.92 / PDF p.100 gives the prime-to-p compatible-frame variant.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft
built 2012-02-08, Chapter X, Definitions (10.25)–(10.26), printed p.150 /
PDF p.154, defines finite étale covers, the geometric-fibre functor and,
for a connected locally noetherian base, its automorphism group as the
algebraic fundamental group. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This is a derived specialization of
[WeilCompactOpenLevelIsogeny](WeilCompactOpenLevelIsogeny.md) to
[GeometricWeilCompactOpenLevels](GeometricWeilCompactOpenLevels.md).
It supplies the latter's actual geometric finiteness proofs to the
former, constructs the resulting full and away natural isomorphisms,
and exposes their coherence laws. The new wrappers and their
coherence specializations are deductions from the published Library
implementations, rather than separate existence assertions in the
literature. All declarations are in
`Langlands.AbelianScheme.Tate.Geometric`.

## Geometric data and retained hypotheses

Let `S : Scheme.{u}` be quasi-separated, and let `A`, `B` and, for
composition, `C` be actual abelian schemes over `S`. Each endpoint has
its `HasDualScheme`, `DualSchemeGeometry`, inverse Poincaré line bundle
and displayed evaluation isomorphism, and an actual homomorphism `lam`
to the resulting constructed dual abelian scheme. These homomorphisms
are general dual-valued maps; the present interface does not certify
that they are polarizations.

The retained tensor/Picard and pairing-construction proposition inputs
are `pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, `PicardZeroPullbackStatement` and
`RelativeFiniteWeilTransitionStatement`. The appropriate
`DualSchemeMapAdditivity` inputs for ordered pairs of endpoints remain
explicit: `AB` for forward transport; `AA` for the identity; `AB`, `BC`
and `AC` for composition; and `AB`, `BA` and `BB` for inverse transport.
As in the generic published module, the pairing functoriality and
geometric pairing-transport inputs are supplied by the proved
`rationalWeilFunctoriality` and `rationalWeilGeometricTransport`.
Neither is an additional hypothesis of this interface.

Let `D` be a rational algebra with actual actions
`iA : D →ₐ[ℚ] Rationalization.End A` and similarly for `B` and `C`.
Let `V : Type w` have compatible rational and `D`-module structures,
and let `ψ` be a rational bilinear form. The full PEL requirements on
this data, including finiteness, faithfulness, alternation and
involution compatibility, are expressed separately by
`RationalPELConditions`. They are not inferred here.

Fix an actual geometric point `s : Spec Ω ⟶ S`, with `Ω : Type u`
an algebraically closed field. The full construction requires
`h : Global.RationalProfiniteIntegerAdeleComparison` and
`hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))`.
It uses all positive torsion orders and coefficient ring
`Global.FiniteAdeles ℚ`. The away construction instead requires
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`
and units only at positive orders coprime to the natural modulus `m`.
Its coefficient ring is `Global.PrimeToFiniteAdeles m`. The ambient
comparison `h` in the away interface does not impose full-order units.
At a prime modulus this is the prime-to-that-prime version;
allowing arbitrary natural moduli extends that application.

The new definitions supply the following published proofs, with no
additional finiteness proposition or finite-étale instance input:

- `geometricFiberFinite s` for finiteness of every actual finite-étale
  cover's geometric fibre;
- `torsionFiniteEtale` for the abelian torsion kernels at the selected
  invertible orders;
- `TateTwist.Geometry.InvertibleOrders.selectedFinite` and
  `selectedEtale` for the actual selected roots-of-unity group schemes,
  using the same `hunit`.

Thus the acting group is exactly
`FundamentalGroup s (geometricFiberFinite s)`. Its definition as an
automorphism group and the construction at this fixed point make sense
under the displayed hypotheses. The connected locally noetherian
hypotheses used for canonical point comparisons and the Harris–Taylor
application are not required for the present fixed-point isogeny laws.

## Natural tower isomorphisms

Write `T_A` and `T_B` for the existing actual geometric full or away
compact-open level towers at `s`. Their index category is
`FiniteAdelicScalarExtensionLevel D V ψ` or
`PrimeToScalarExtensionLevel D V ψ m`. Its objects are actual compact
open subgroups of the corresponding scalar-extension similitude group.
At `K`, the tower consists of monodromy-fixed right `K`-orbits of
actual compatible frames. Fixedness is a property of the orbit class;
a fixed representative is not required.

These frames are the existing scalar-linear isomorphisms to the
rationalized actual torsion inverse limit. Pairing compatibility uses
the Poincaré-derived pairing pulled back along `lam` and existentially
quantifies a linear trivialization of the actual rational Tate twist.
The same scalar comparison acts on both the rationalized Tate module
and the twist. No roots of unity, independent pairing, independent
monodromy action or frame trivialization are chosen by this module.

Let `e : Rationalization.of A ≅ Rationalization.of B` be an actual
invertible rational homomorphism and `q : ℚˣ`. Assume that `e`
intertwines `iA` and `iB` and satisfies the actual dual-homomorphism
identity

`e^∨ lamB e = q lamA`.

The exact predicate is `IsRationalDualPullbackMultiple`, formed with
the constructed rational dual homomorphism and `Rationalization.ofHom`
of the displayed integral dual-valued maps. The identity is geometric
homomorphism data, not an assumed equality between arbitrary forms.

`weilAdelicCompactOpenLevelIsogeny` and
`weilPrimeToAdelicCompactOpenLevelIsogeny` construct `T_A ≅ T_B`.
Their definitions apply the corresponding published natural isogeny
comparison with the geometric proofs above. The inherited fixed-level
equivalence postcomposes compatible frames with the actual rational
Tate map of `e`, then descends through the commuting right and
geometric actions to invariant orbit classes.

The `_hom_app` and `_inv_app` theorems identify the forward and inverse
components at `K` with the corresponding published
`weilAdelicLevelIsogeny` or `weilPrimeToAdelicLevelIsogeny` equivalence
and its inverse. Both formulas are proved by reflexivity.
The `_arrow` theorems state, for every transporter arrow `a : K ⟶ L`,

`Isogeny(L)(T_A(a)(x)) = T_B(a)(Isogeny(K)(x))`.

They follow from `NatTrans.naturality_apply`. The transporter convention
is precomposition of frames by an element `g` satisfying
`g⁻¹ K g ≤ L`. In particular the theorem includes level-forgetting
arrows.

With `[Module.Finite ℚ V]`, the `_heckeLeft` and `_heckeRight` theorems
spell out this square for both existing compact-open Hecke arrows.
The intermediate subgroup is `K ∩ g L g⁻¹`; its first arrow is the
inclusion into `K`, and its second has transporter element `g` and
lands in `L`. These two proofs are also `naturality_apply` for the
constructed natural isomorphism. The maps are the existing tower maps,
so their source levels and right-action convention are preserved.

## Multiplier and isogeny coherence

For both full and away towers, `_Isogeny_refl` identifies transport by
the actual identity rational isogeny with `Iso.refl T_A`. Its algebra
intertwining equation is `rationalIntertwines_identity`, and its unit
multiplier equation is `IsRationalDualPullbackMultiple.id`.

`weilAdelicCompactOpenLevelIsogenyComp` and its away analogue apply the
published direct-composite construction to `e.trans f` with multiplier
`q*r`. The intertwining equation is derived by
`rationalIntertwines_comp`, and the geometric multiplier equation by
`IsRationalDualPullbackMultiple.comp`. The corresponding
`_IsogenyComp_eq_trans` theorem identifies direct composite transport
with the composite of the two natural isomorphisms, first for `e`
and then for `f`. The intermediate abelian scheme and all its data
are shared by both constructions.

`weilAdelicCompactOpenLevelIsogenyInverse` and its away analogue apply
the published inverse construction to `e.symm` with multiplier `q⁻¹`.
The reverse intertwining equation and geometric multiplier equation are
derived by `rationalIntertwines_inverse` and
`IsRationalDualPullbackMultiple.inv`. The `_Isogeny_symm` theorem
identifies this direct inverse transport with the inverse of forward
transport.

The new identity, composition and inverse proofs specialize the
corresponding proved theorems of `WeilCompactOpenLevelIsogeny`. Their
inherited proofs reduce natural-isomorphism equality to equality of
fixed-level equivalences, whose identities are proved by descending the
actual compatible-frame identities. No extra identity, composite or
inverse pairing equation is supplied as a hypothesis.

This unit compares specified actual rational isogenies over one base
and one geometric point. It asserts no rank, chosen basis, existence
of compatible frames, positivity, polarization or nondegeneracy.
Canonical changes of geometric point and pointed base change are
provided by separate modules; their mixed compatibility with isogeny
transport is not a new assertion of this unit. The PEL moduli functor
remains outside this construction.
