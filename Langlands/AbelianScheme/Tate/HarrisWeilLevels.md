# Harris trace-form indices for actual Weil level towers

This derived specialization connects `PEL.ScalarExtensionRegular` to
`Tate.WeilCompactOpenLevels`. It proves the rational PEL source conditions
for the existing inverse-unit Harris trace form, transports actual compact
open subgroups and transporter arrows, and uses the transported indices in
the actual full and away Weil level towers. It constructs neither a moduli
functor nor a polarization.

The geometric conventions come from Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), printed p.18 / PDF
p.26, and Section III.1, printed pp.91–92 / PDF pp.99–100: rationalization
of the actual torsion inverse limit, monodromy-fixed orbits of compatible
frames, and the right level action. The new source-condition theorem,
reindexing and Hecke formulas are internal deductions from the imported
Library results. The trace and involution conventions are those already
implemented and documented in `PEL.TracePairing`, `PEL.HarrisPositiveInput`
and `PEL.ScalarExtensionRegular`.

## Rational source and original Harris group

Retain the actual `CentralSimpleUnitaryData E K B n`, with its totally real
number field E, totally complex quadratic extension K, algebra structures
and scalar towers displayed in Lean. Write σ for the original involution
and let β be a unit with σ(β) = −β. Set

`τ = D.skewTwist β hβ`,

`ψ = τ.tracePairing β⁻¹`.

Thus τ has involution b ↦ β σ(b) β⁻¹ and ψ(x,y) is the published normalized
rational trace of x β⁻¹ τ(y). The source module is B with its regular left
B-action. The left-adjoint involution of ψ is τ's rational involution; the
original σ is its right adjoint. These roles are retained in this module.

`harrisRationalPELConditions` proves the published predicate
`RationalPELConditions` for τ and ψ. It derives finite dimension over E
from `D.totallyRealBasis`, and finite dimension over ℚ by transitivity.
The regular module supplies the scalar tower and faithful action.
Alternation follows by applying the existing trace-form alternation
theorem to β⁻¹, using `skewAdjoint_inverse_skew`. Nondegeneracy and the
left-involution identity are the corresponding existing trace-form
theorems. No new nondegeneracy hypothesis is imposed.

`harrisPositiveRationalPELConditions` specializes this proof to the
published `harrisPositivePELUnit` selected from Harris signature charts.
The charts remain inputs; the proved positive-twist existence theorem is
used through `HarrisPositiveInput`. The conclusion is the rational PEL
predicate for `harrisPositivePELAlgebra` and `harrisPositivePELForm`.
Hodge positivity and the existence of signature charts are not conclusions
of this theorem.

For R equal to `FiniteAdeles ℚ` or `PrimeToFiniteAdeles m`, the published
continuous group equivalence has type

`e : (D.toSecondKindInvolution.rationalInvolution.Points R)ᵐᵒᵖ ≃ₜ*`
`ScalarExtensionSimilitudePoints B B R ψ`.

Its actual operator is `e(g)(x) = x * g.unop.val.1`. Its multiplier is the
original σ-group multiplier, by the imported
`harrisScalarExtensionContinuousEquiv_multiplier` theorem. The opposite
source is essential for this to be a group equivalence. All conjugations
and products of Harris index elements below take place in that opposite
group; in particular `(g * k).unop = k.unop * g.unop`.

## Compact-open indices

`harrisWeilFiniteAdelicLevelFunctor` applies the published
`CompactOpenLevel.transportFunctor` to the full equivalence e. Its object
at U is the compact open subgroup e(U), implemented as the inverse image
of U under e⁻¹. Its arrow at a transporter f has element e(f.element).
The `_obj_mem` and `_map_element` formulas identify these objects and
elements. The `_inclusion` formula identifies an inclusion arrow with the
actual inclusion between the transported subgroups; its proof uses arrow
extensionality and e(1) = 1.

`harrisWeilPrimeToLevelFunctor` and its corresponding formulas do the
same over `PrimeToFiniteAdeles m` for every natural modulus m.

The two `_heckeLevel` theorems identify the transported intermediate
compact open subgroup with

`e(U ∩ g W g⁻¹) = e(U) ∩ e(g) e(W) e(g)⁻¹`.

They reuse the generic transport theorem. Their local finite rational
module instance is derived from `harrisRationalPELConditions`; users need
not supply an independent finite-dimensionality assumption to form these
Hecke intersections.

## Actual full Weil level tower

The geometric inputs are an actual abelian scheme A over a quasi-separated
scheme S; its constructed dual geometry; a line bundle inverse to the
Poincaré family with evaluation isomorphism; and the displayed homomorphism
`polarizationMap` into the resulting dual abelian scheme. The latter is
only a dual-valued homomorphism in this interface, with no assertion that
it is a polarization. The action `i : B →ₐ[ℚ] Rationalization.End A`, a
field-valued point s, and finite fibres of the actual finite-étale fibre
functor at s are also explicit.

The named pullback-tensor preservation, composition, unit, associativity,
unitor and symmetry statements, `PicardZeroPullbackStatement`,
`RelativeFiniteWeilTransitionStatement` and
`TorsionFiniteEtaleStatement` remain hypotheses. The full scalar comparison
`RationalProfiniteIntegerAdeleComparison` is supplied, every selected
positive torsion order is invertible on S, and the corresponding roots of
unity schemes are assumed finite and étale. This interface is more general
than the connected locally noetherian characteristic-zero setting of the
cited moduli problem; it does not prove those additional moduli conditions.

`HarrisWeilAdelicLevel U` is the existing actual full compact-open Weil
level at e(U). In the imported construction the rational Tate module is
ℚ ⊗[ℤ] the actual integral torsion inverse limit. Its finite-adelic action
and the actual rational Tate twist use the same supplied scalar
comparison. Compatible frames are linear for B ⊗[ℚ] R and identify ψ after
scalar extension with the actual Weil pullback through an existential
R-linear trivialization of the twist. Relative to any specified
trivialization this is preservation up to an R-unit. No trivialization is
chosen as part of a frame. The level is the subset of monodromy-fixed
right orbit classes, rather than a set of fixed representatives.

`harrisWeilAdelicLevelTower` is the composite of the Harris index functor
with `weilAdelicCompactOpenLevelTower`. The imported tower installs the
proved `rationalWeilGeometricTransport`; it does not require an extra
arbitrary geometric pairing action. Its object formula is definitional.
Its map formula is the published fixed-level translation by e(f.element),
using the transported conjugation condition. Identity and composition
are the functor laws of this composite with the existing transporter
multiplication order.

`harrisWeilAdelicFrameRightAction_apply` identifies the action on actual
compatible frames as

`(eta * e(g))(x) = eta(x * g.unop.val.1)`.

This follows by definition from the imported frame action and regular
Harris operator. It needs no torsion finite-etaleness or roots-of-unity
instances beyond the data required to define a frame. The `_inclusion`
theorem identifies a tower inclusion map with the actual fixed-level
forgetting map, by rewriting the transported arrow inclusion.

`harrisWeilAdelicHeckeLeft` and `harrisWeilAdelicHeckeRight` are the two
tower maps from the level at U ∩ g W g⁻¹. Their finite module instance is
again derived from the source theorem. The `_eq` lemmas identify the first
leg with forgetting the transported intermediate subgroup and the second
with translation by e(g). The first proof applies the tower inclusion
formula; the second is definitional. Together with the index intersection
comparison, these describe the actual Hecke span without changing the
opposite-group convention or the multiplier.

## Away version and scope

`HarrisWeilPrimeToAdelicLevel`, `harrisWeilPrimeToAdelicLevelTower`, the
frame-action formula, inclusion formula and both Hecke legs implement the
same constructions over `PrimeToFiniteAdeles m`. They use the coupled
`PrimeToRationalProfiniteIntegerAdeleComparison h m` for the actual away
Tate module and its twist. Torsion orders are positive integers coprime to
m, and invertibility and finite étale roots-of-unity hypotheses are
restricted to exactly those orders. At a prime modulus this is the
prime-to-p case; no primality is required for the construction.

These towers keep the actual geometric objects and their monodromy.
No compatible-frame nonemptiness, positivity or nondegeneracy of an
arbitrary `polarizationMap`, determinant condition, quotient of abelian
schemes by rational isogenies, or representability assertion is proved.
The complex double-quotient tower in `PEL.TraceSimilitudesLevels` is a
separate consumer of the same algebraic comparison. This module supplies
the actual Tate/Weil consumer with the opposite index convention stated
above, without identifying it with that complex tower or with the entire
Harris–Taylor moduli functor.
