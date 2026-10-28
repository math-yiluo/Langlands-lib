# Coefficient equivalences of intrinsic weighted rational quotients

Worker 56 derives this specialization from the actual relative-series
quotients and bounded coefficient transport. All declarations belong to
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation`.

## Inputs and actual quotients

Let `K` be an ultrametric normed field, and let `A`, `B` be actual
`PresentedAffinoidAlgebra K` objects. Fix a natural number `m`, arbitrary
positive real radii `s : PositivePolyradius (Fin m)`, and actual elements
`g : A`, `f : Fin m → A`. Supply a bounded algebra equivalence
`e : BoundedAlgEquiv K A B`. This is an actual `K`-algebra equivalence
with proved boundedness of its forward and inverse maps; it need not be
an isometry.

Writing `R_s(A;g,f)` for `Algebra K A s g f`, the source is the concrete
normed quotient

\[
 R_s(A;g,f)=A\{s^{-1}Y\}/
   \overline{\langle C(g)Y_j-C(f_j):j\in\operatorname{Fin}m\rangle}.
\]

The target is `R_s(B;e(g),e(f))` with the same positive radii and coordinate
labels. The closure and quotient norms are the actual ones from the
published `RelativeRelations` construction. No desired quotient map,
inverse, relation-compatibility proof, or spectral comparison is an input.

## Construction and formulas

`coefficientEquiv_mapsRelations` applies the coefficient transport
generator computation to `e.toBoundedAlgHom`. Each rational generator
maps to the corresponding generator with coefficients `e(g)` and `e(f_j)`,
and hence lies in the target closed generated ideal.

`coefficientEquiv_symm_mapsRelations` applies the same computation to
`e.symm.toBoundedAlgHom` and the mapped data. The proved identities
`e.symm(e(g)) = g` and `e.symm(e(f_j)) = f_j` identify the resulting
equations with the original ones. Thus both compatibility directions
are discharged from the actual coefficient equivalence.

`coefficientEquiv` applies the generic
`RelativeRelations.transportEquiv` with these two proofs. That generic
construction descends the actual coefficientwise series maps and proves
their inverse identities using quotient surjectivity and the coefficient
inverse identities. The rational specialization assumes neither inverse
identity. `coefficientEquiv_toBoundedAlgHom` identifies its forward bounded
map with `transport K s g f e.toBoundedAlgHom`.

The two `coefficientEquiv_quotientMap` formulas compute both directions
on every relative-series representative:

\[
 E(q_A(h))=q_B(e_*(h)),\qquad
 E^{-1}(q_B(k))=q_A((e^{-1})_*(k)).
\]

Here `q_A`, `q_B` are the corresponding rational quotient projections,
and coefficientwise maps are `mapCoefficientsAlgHom`. The two
`coefficientEquiv_baseMap` formulas state

\[
 E(\iota_A(a))=\iota_B(e(a)),\qquad
 E^{-1}(\iota_B(b))=\iota_A(e^{-1}(b)).
\]

The forward and inverse `coefficientEquiv_fraction` formulas preserve
each coordinate label `j`. These computations specialize the generic
quotient transport formulas.

`eq_coefficientEquiv` characterizes the forward bounded map among all
bounded algebra homomorphisms with the displayed coefficient and fraction
values. It applies the rational transport uniqueness theorem, which
rests on coefficient/fraction extensionality. `coefficientEquiv_refl`
and `coefficientEquiv_trans` prove the pointwise identity and composition
laws, respectively, by evaluating the corresponding transport laws.
The latter allows a third actual presented algebra `C` and a bounded
equivalence `d : BoundedAlgEquiv K B C`; it states that the induced map
for `e.trans d` equals the successive induced maps on every quotient
element.

## Bounds and isometry

`norm_coefficientEquiv_le` transfers each supplied real constant `c ≥ 0`
such that `‖e(a)‖ ≤ c * ‖a‖` to the actual quotient norms with the same
constant. `norm_coefficientEquiv_symm_le` does so independently for any
bound on `e.symm`. These are the generic quotient equivalence bounds;
their zero-constant case remains valid, including for zero quotients.

`norm_coefficientEquiv` assumes `‖e(a)‖ = ‖a‖` for every coefficient
and proves exact preservation of the rational quotient norm. The generic
proof uses contraction in both directions and the proved quotient
inverse identities. `norm_coefficientEquiv_symm` then evaluates this norm
equality at the inverse image and uses the forward inverse identity.
`isometry_coefficientEquiv` transfers an actual `Isometry e` by the
generic quotient isometry theorem. Arbitrary bounded equivalences still
produce bounded quotient equivalences; their norms are not asserted
equal without the norm-preservation hypothesis.

## Actual spectra and inequality loci

`coefficientSpectrumHomeomorph` is the genuine contravariant
homeomorphism induced by `coefficientEquiv`:

\[
 \mathcal M(R_s(B;e(g),e(f)))\simeq
 \mathcal M(R_s(A;g,f)).
\]

The forward evaluation formula is `x ↦ x ∘ E` and the inverse formula
is `x ↦ x ∘ E.symm`, expressed by the two
`coefficientSpectrumHomeomorph_apply` lemmas. The spectrum has its
actual pointwise topology. The construction uses boundedness in both
directions and requires no isometry assumption.

`coefficientLocusHomeomorph` restricts `e.spectrumHomeomorph` to the
coefficient-spectrum subsets

\[
 \{x\in\mathcal M(B):x(e(f_j))\le s_j x(e(g))\}
 \ \simeq\
 \{x\in\mathcal M(A):x(f_j)\le s_j x(g)\}.
\]

Membership in the mapped-data locus is definitionally equivalent to
membership in the original locus after pullback. The definition supplies
this predicate equivalence to `Homeomorph.subtype`. That construction
inherits the inverse laws and continuity in both directions from the
coefficient spectrum homeomorphism, whose inverse uses the proved
coefficient inverse identities. The two `coefficientLocusHomeomorph_apply` formulas are
`x(e(a))` and `x(e.symm(b))`, respectively.

`coefficientSpectrumHomeomorph_naturality` states that the actual
structural map from the mapped quotient spectrum to its inequality
locus, followed by `coefficientLocusHomeomorph`, equals the structural
map from the original quotient spectrum after
`coefficientSpectrumHomeomorph`. This is an equality of continuous
maps. The proof applies extensionality for continuous maps, subtypes
and spectrum points, then the forward coefficient formula.

## Original source, derivation and scope

The original source is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, retained PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF pages 8–9 were read directly. Definition 2.1.6(i), page 8,
gives relative restricted series with positive radii and the weighted
maximum norm. Definition 2.1.11 there uses bounded algebra homomorphisms
and the dual direction for spectra. Exercise 2.2.2(ii), page 9, gives
the rational equations and inequalities. The coefficient equivalence
and all the comparison laws here are internal derivations, not a
numbered theorem quoted from that source.

The construction works without completeness of `K`, nontrivial valuation,
proper relation ideals, nonzero quotients, nonempty variable blocks, or
restrictions on the positive radii. It does not assume that `g,f_j`
generate the unit ideal. The source's rational-domain representability
assertion is not inferred under these weaker hypotheses.

The module transports a supplied actual bounded coefficient equivalence.
It does not construct equivalences between arbitrary coefficient
presentations, compare scalar rational models, prove denominator
invertibility or a reverse structural map from a rational inequality
locus, or construct analytic domains, atlases, sheaves or etale sites.
