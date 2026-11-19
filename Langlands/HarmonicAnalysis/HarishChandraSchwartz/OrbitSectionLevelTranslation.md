# Translation of orbit sections at a fixed level

This derived module bounds translation in the existing seminorm topology
of `OrbitSectionLevel`. It uses the full product action already defined
in `ProductInducedOrbitFullAction`. The bounds support the finite
translation step of Waldspurger's proof of Proposition VI.3.1, printed
pp. 302–303. [Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)

For a section fixed by `H × H` and an ordered pair `x = (x₁, x₂)` of
ambient group elements, `orbitSectionTranslatedLevel` takes the
intersection of `K`, `x₁ H x₁⁻¹`, and `x₂ H x₂⁻¹`.
`orbitSectionLevelTranslate` restricts the original full action to a
complex-linear map into that level. Membership in each conjugate ensures
that the corresponding factor of the product action fixes the translated
section. Extension to the space of all smooth orbit sections recovers the
full action.

`exists_orbitSectionLevelTranslate_seminorm_bound` bounds each original
derivative seminorm of the translated section by a finite supremum of the
input seminorms times a nonnegative constant. The proof works at the
translated level, where the compact restriction is right invariant under
the intersection of its product level with `K × K`. One evaluation per
class of the resulting finite quotient jointly determines the compact
restriction. By linear extension from the image of that finite tuple,
any ambient dual functional on the fixed space is a sum of dual
functionals applied to those evaluations.

At each of those points the published full action formula gives one
smooth Laurent scalar times the original compact restriction evaluated
at another point and composed with a fixed linear map. The derivative
of each product is bounded by the finite Leibniz estimate in
`TorusMonomialSeminormControl`. The union of the resulting derivative
indices works for every input section at the given level.

`continuous_orbitSectionLevelTranslate` follows using the existing
seminorm families. The same argument and the seminorm bound for
continuous seminorms give `exists_orbitSectionLevelTranslate_finsetSup_bound`
for any finite collection of output derivative indices. The construction
uses the given Laurent unitary coordinates and original compact picture.
It applies before choosing a packet weight or measure.
