# Isometric interchange of weighted rational intersection factors

`swapEquiv` constructs a bounded algebra equivalence between the two actual
product rational quotients obtained by reversing the factors. It fixes the
coefficient algebra, transposes the fraction coordinates, and preserves the
actual quotient norms. All declarations lie in
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection`.

## Source and provenance

The source context is Berkovich, *Non-archimedean analytic spaces* (Trieste
lectures, 2009), Definition 2.1.6(i), printed/PDF page 8, and Exercise
2.2.2(ii),(iii), printed/PDF page 9. These passages specify weighted restricted
series, rational quotients, and intersections of rational domains. The registered
source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

The explicit product presentation and transposition equivalence are internal
derivations. The proof uses the published `RationalIntersection`, its actual
closed scalar rational quotient, the isometric `relativeEquiv`, and convergent
`RelativeRationalPresentation.evaluate`. The source does not state this precise
norm-preserving comparison of the chosen scalar presentations. Its full
affinoid-domain factorization property in Definition 2.2.1 remains a separate
obligation.

## Inputs and quotient coordinates

Let `K` be an ultrametric normed field, `A : PresentedAffinoidAlgebra K`, and
let `s : PositivePolyradius (Fin m)` and
`t : PositivePolyradius (Fin n)` be arbitrary finite positive polyradii.
Choose representatives `g`, `h`, `f i`, and `k j` in
`GeneralizedTateAlgebra A.polyradius K`. Write
\[
 F=(g,f_0,\ldots,f_{m-1}),\quad H=(h,k_0,\ldots,k_{n-1}),\qquad
 S=(1,s_0,\ldots,s_{m-1}),\quad T=(1,t_0,\ldots,t_{n-1}).
\]
A bar denotes the image under `presentationMap K A`.

The imported `Algebra K A s t g h f k`, denoted `D`, is the actual scalar
rational quotient with denominator `g * h`, all numerators `F_i * H_j`, and
radii `S_i * T_j`. Its quotient coordinates `Z_ij = fractionCoordinate ... i j`
satisfy
\[
 \operatorname{base}(\overline{gh})Z_{ij}
   =\operatorname{base}(\overline{F_iH_j}),\qquad
 \|Z_{ij}\|\le S_iT_j.
\]
The reversed presentation `D' = Algebra K A t s h g k f` has denominator
`h * g`, numerators `H_j * F_i`, radii `T_j * S_i`, and coordinates `Z'_ji`.
Both presentations use their actual closed quotient norms throughout.

`swapTuple` assigns each encoded index `(i,j)` of `D` to `Z'_ji` in `D'`.
The pair is encoded with `finProdFinEquiv`. `swapTuple_pair` records this formula.
`norm_swapTuple_le` uses commutativity of real multiplication to obtain the
original product-radius bound. `swapTuple_equation` uses commutativity in the
scalar series algebra to prove the original rational equation for that tuple.
These constructions and estimates do not require completeness or generation.

## Constructed maps, inverse, and norms

For the remaining constructions assume `[CompleteSpace K]`.
`swapMap : BoundedAlgHom K D D'` first applies the published scalar-to-relative
isometric comparison `relativeEquiv`, then evaluates relative series at the
coefficient map `base K A t s h g k f` and tuple `swapTuple`.

The coefficient map is contractive. The private `swapTuple_monomial` estimate
follows from the proved coordinate bounds and the imported target bound
`PresentedAffinoidAlgebra.norm_one_le`. This includes the empty monomial in a
zero quotient. `swapTuple_equation` supplies the rational relations needed for
the evaluation to descend through the closed quotient.

`swapMap_base` and `swapMap_fractionCoordinate` prove
\[
 \operatorname{swapMap}(\operatorname{base}(a))=\operatorname{base}'(a),\qquad
 \operatorname{swapMap}(Z_{ij})=Z'_{ji}.
\]
`norm_swapMap_le` combines the evaluation estimate with norm preservation of
`relativeEquiv`, so the constructed map is contractive.

Applying the same construction to the reversed data gives a contractive map
`D' -> D`. `swapMap_comp_swapMap` proves that its composite with `swapMap`
is the identity by the published scalar rational `hom_ext`: the two maps agree
on every coefficient and fraction coordinate. `swapMap_involutive` is the
pointwise form. Applying it with reversed inputs supplies the other inverse
identity.

`swapEquiv` packages these two constructed maps with `BoundedAlgEquiv.ofHomInv`.
`swapEquiv_apply` and `swapEquiv_symm_apply` identify its forward and inverse
maps. The two contractive bounds and inverse identities imply
`norm_swapEquiv` and `norm_swapEquiv_symm`, the exact norm equalities in both
directions. `isometry_swapEquiv` follows by applying the standard norm-preserving
additive-map criterion. No inverse, norm equality, or evaluation certificate is
assumed.

## Spectrum and restriction formulas

`swapSpectrumHomeomorph : BanachSpectrum D' ≃ₜ BanachSpectrum D` is the actual
contravariant spectrum homeomorphism of `swapEquiv`. Its forward map sends
`x` to the seminorm `a ↦ x (swapMap a)`; its inverse uses the reversed map.
These are the two `swapSpectrumHomeomorph_*apply` formulas.
`swapMap_comp_base` and `swapSpectrumHomeomorph_naturality` express that the
coefficient map, and hence the structural map to `BanachSpectrum A`, is fixed.

For the rest of the module also assume the original explicit hypotheses
`hf : GeneratesUnitIdeal K A g f` and
`hk : GeneratesUnitIdeal K A h k`, namely
\((\bar g,\bar f_i)=A\) and \((\bar h,\bar k_j)=A\).
The imported left and right restrictions exist under these hypotheses.
`swapMap_comp_leftMap` and `swapMap_comp_rightMap` show that the swap exchanges
them with the right and left restrictions of the reversed presentation. The
proof again uses coefficient/fraction extensionality and the transposition
formula. `leftSpectrumMap_swapSpectrumHomeomorph` and
`rightSpectrumMap_swapSpectrumHomeomorph` give the corresponding equalities of
continuous contravariant spectrum maps.

Finally, `intersectionHomeomorph_swapSpectrumHomeomorph` proves that the two
published intersection identifications give the same underlying point of
`BanachSpectrum A` after swapping. Their codomains are the two orderings of the
intersection; the theorem compares their underlying seminorms.

## Scope

The equivalence and spectrum homeomorphism need no unit-generation hypothesis;
`hf` and `hk` enter only the restriction-exchange and intersection-identification
formulas. There is no radius ordering, nontrivial-valuation, proper-ideal,
nonzero-quotient, or nonempty-block assumption. The result compares the two
specified presentations; independence from arbitrary scalar representatives is
not asserted. Bounded pushouts, iterated rational comparisons, general
spectral-image factorization, analytic atlases and sheaves, and etale or
equivariant sites remain separate constructions.
