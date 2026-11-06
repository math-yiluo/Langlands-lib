# Closed-ideal effectiveness for the actual binary Laurent diagram

This is an internal prerequisite for finite-cover closed-ideal descent. It
applies the abstract theorem of `SplitSquareIdealDescent` to the binary Laurent
diagram of the Library module `BinaryLaurentDiagram`. The motivating source is
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 / PDF p.12, registered as
`berkovich-1993-etale-cohomology`; its use is recorded in the paired Markdown of
`FiniteDomainIdealDescent`. The splitting and density arguments below are
internal; they use the published normal form of the relative unit annulus and
transcribe no particular proof from the source.

Throughout, `K` is a complete ultrametric normed field, `A` is a presented
affinoid `K`-algebra with an arbitrary positive polyradius, and `f ∈ A`. No
nontrivial valuation is assumed except in the two strict declarations at the
end. The diagram is the Library's:

- `Upper K A f = A⟨X⟩ / closure(X - f)`, the relative rational quotient with
  denominator `1` and numerator `f`;
- `Lower K A f = A⟨Y⟩ / closure(fY - 1)`, the relative rational quotient with
  denominator `f` and numerator `1`;
- `Overlap K A f = A⟨X,Y⟩ / closure(X - f, fY - 1)`;
- the coefficient maps `upperBase`, `lowerBase`, `overlapBase` and the
  restrictions `left : Upper → Overlap` and `right : Lower → Overlap`.

All series rings have unit radius, and all quotients carry their quotient norms.

## Transfer of Noetherianity and closed ideals

`BoundedAlgEquiv.isClosed_ideal`: if every ideal of `B` is closed and `e` is a
bounded algebra equivalence from `B` to `C`, then every ideal of `C` is closed.
An ideal `I` of `C` is the inverse image of the closed ideal `e⁻¹(I)` under the
continuous map `e⁻¹`.

In the namespace `PresentedAffinoidAlgebra.RelativeRationalPresentation`:

- `exists_boundedAlgEquiv`: every intrinsic relative rational quotient
  `Algebra K A s g f` is boundedly equivalent to some presented affinoid algebra.
  The proof chooses series representatives of `g` and of each `f j` (the
  presentation map is surjective) and uses the Library equivalence
  `RationalPresentation.relativeEquiv`.
- `isNoetherianRing` and `isClosed_ideal`: hence every such quotient is
  Noetherian, and all its ideals are closed. Both facts are transported from
  the Library results for presented affinoid algebras in
  `GeneralizedAffinoid.Noetherian`.

In the namespace `PresentedAffinoidAlgebra.BinaryLaurent`,
`isNoetherianRing_upper`, `isNoetherianRing_lower`, `isClosed_upper_ideal` and
`isClosed_lower_ideal` are the special cases for `Upper` and `Lower`.
`isClosed_overlap_ideal` applies the transfer to the Library equivalence
`productOverlapEquiv` from the four-variable relative rational quotient
`ProductOverlap` to `Overlap`.

## Bounded splitting of the overlap

`exists_split`: every `o ∈ Overlap K A f` equals `left h₁ + right h₂` with
`‖h₁‖ ≤ 2‖o‖` and `‖h₂‖ ≤ 2‖o‖`.

The case `o = 0` is trivial. Otherwise, `exists_toOverlap_norm_lt` gives an
element `z` of the relative unit annulus `A⟨X,Y⟩ / closure(XY - 1)` with
`toOverlap z = o` and `‖z‖ < 2‖o‖`. The published normal form is an isometry `e`
from the annulus onto `C₀(ℤ, A)`. Let `r` be the unit-radius series whose `k`-th
coefficient is `e z k`, and `s` the series whose `k`-th coefficient is
`e z (-k-1)` (`upperSeries` and `lowerSeries`). Comparing coefficients through
`e` gives `z = positive r + Y · negative s` in the annulus. Coefficient bounds
give `‖r‖ ≤ ‖z‖` and `‖s‖ ≤ ‖z‖`, because the unit-radius norm is the supremum
of the coefficient norms.

Take `h₁` to be the image of `r` in `Upper`, and `h₂ = Y · (image of s in Lower)`.
The Library identities `toOverlap_positive`, `toOverlap_negative` and
`toOverlap_annulusY` give `o = left h₁ + right h₂`. The quotient maps are
contractive and `‖Y‖ ≤ 1` in `Lower`, so `‖h₁‖, ‖h₂‖ ≤ ‖z‖ ≤ 2‖o‖`.

## Dense range of the right restriction

`left_mem_closure_range_right`: `left h` lies in the closure of the range of
`right` for every `h ∈ Upper`. Write `h` as the image of a unit-radius series,
which is the sum of its monomials (`hasSum_monomials`). The image of a monomial
`a Xᵏ` in `Overlap` is `overlapBase a · Xᵏ = overlapBase (a fᵏ)`, since `X = f`
there (`overlapX_eq`). This equals `right (lowerBase (a fᵏ))`. So the partial
sums lie in the range of `right`, and their limit `left h` lies in its closure.

`denseRange_right`: by `exists_split`, every overlap element is
`left h₁ + right h₂`. The closure of the additive range of `right` is an
additive subgroup containing both summands.

## The split square and effectiveness

`splitSquare hglue` is the `BoundedAlgHom.SplitSquare` structure for the square
`upperBase`, `lowerBase`, `left`, `right`. It takes as hypothesis `hglue`: if
`left s = right t`, then some `a ∈ A` has `upperBase a = s` and
`lowerBase a = t`. Its fields are the commutation `left_upperBase` and
`right_lowerBase`, the gluing hypothesis, `denseRange_right`, the constant `2`,
and `exists_split`.

`closedIdealMap_inf_comap_eq_of_gluing hglue`: let `I₁` be an ideal of `Upper`
and `I₂` an ideal of `Lower`, and suppose
`left.closedIdealMap I₁ = right.closedIdealMap I₂`. Let
`J = upperBase⁻¹(I₁) ⊓ lowerBase⁻¹(I₂)`. Then
`upperBase.closedIdealMap J = I₁` and `lowerBase.closedIdealMap J = I₂`. This is
`SplitSquare.closedIdealMap_inf_comap_eq` applied to `splitSquare hglue`, using
the Noetherian and closed-ideal facts above. Completeness of `Upper` and
`Lower` is the Library's instance for these quotients.

`splitSquareOfStrict hK P f` and `closedIdealMap_inf_comap_eq_ofStrict hK P f`
are the same results for the base `ofStrict K P` of a presented strict
affinoid algebra `P`, assuming `hK : ∃ c : K, 1 < ‖c‖`. Here the gluing
hypothesis is the existence part of the published `BinaryLaurent.gluing`.

## Scope

The effectiveness theorem is stated only for the two-member binary Laurent
cover given by one element `f`. For an arbitrary presented base it assumes
element gluing. The unconditional versions require a strict base and a
nontrivially normed field, because the published gluing theorem does. This
module does not prove the finite-cover `IdealEffectivenessStatement`. It
assumes no reducedness, nonzero algebra or nonempty spectrum, and `f` is
arbitrary, including `0`.
