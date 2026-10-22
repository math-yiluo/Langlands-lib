# Banach rings from positive-polyradius quotient presentations

Author: Worker 56.

Over a complete ultrametric normed field `K`, this module proves that every
`PresentedAffinoidAlgebra K` is complete for its existing quotient norm.
The carrier remains the actual quotient of the finite positive-polyradius
Tate algebra by the presentation's closed ideal. The proof imports
`GeneralizedTateAlgebra.instCompleteSpace` and uses Mathlib's completeness
instance for the quotient. It adds neither a new norm nor a completeness
assumption on the quotient itself. Closedness of the ideal already supplies
the separated norm in `GeneralizedAffinoid.Definitions`.

The functor `PresentedAffinoidAlgebra.toBanachRing` sends each presentation
to its complete normed commutative quotient ring and sends each bounded
`K`-algebra homomorphism to its underlying bounded ring homomorphism.
The identity and composition equations follow from these definitions.
The functor is faithful: equality of the underlying ring maps implies
pointwise equality and hence equality of the original algebra maps.
`toBanachRing_map_apply` records that the function on elements is unchanged.

The equality `affinoidSpectrumFunctor_eq_toBanachRing` identifies the
existing spectrum functor with the composite of this opposite forgetful
functor and `banachSpectrumFunctor`. Both sides use the same actual
bounded multiplicative seminorms, evaluation topology and pullback maps;
this equality is definitional, including equality of functor laws by proof
irrelevance.

There is no assumption on nontriviality of the valuation, and the positive
real radii need not belong to a value group. Zero presentation variables and
the unit ideal are allowed. This is a construction for chosen quotient
presentations; it does not supply analytic atlases, domains, or a sheaf.

The construction is derived from Berkovich, *Non-Archimedean analytic spaces*
(Trieste lectures, 2009): Definition 1.2.1(ii), printed/PDF page 3, defines
completeness in a Banach ring; Example 1.2.2(v), page 4, gives weighted
restricted-series Banach rings; the opening paragraph of section 2.1 and
Definition 2.1.2, page 7, describe the quotient norm and affinoid
presentations. Definitions 1.2.3 and 1.2.5, page 4, give the spectrum and its
evaluation topology. These pages were read directly. Completeness is an
implemented consequence of the imported weighted-series theorem and quotient
completeness. The forgetful functor and its spectrum equality are internal
categorical packaging of those constructions, not separately stated results
from the source.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
