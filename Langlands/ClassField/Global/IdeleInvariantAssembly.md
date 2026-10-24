# Conditional assembly of the global invariant family

This derived supporting construction assembles the regular-class invariant
and the auxiliary cyclic descent into a family on all actual idele-class
cohomology groups. Its provenance is Artin–Tate, *Class Field Theory* (2009),
Chapter VII §3, printed pp.49–50, Lemmas 5–6 and the argument preceding
Theorem 7. The construction uses number fields in any common universe.
It does not prove `GlobalInvariantStatement`.

The inputs remain explicit:

- A family `s` of additive maps on actual idele `H²`, vanishing on the
  actual quotient kernel, preserving inflation and multiplying under
  restriction by the base-extension degree.
- Full denominator range for this idele family on every cyclic extension,
  expressed by the internal proposition `IdeleInvariantMaps.CyclicRange`.
- The published `IdeleClassGaloisDescent`, `IdeleClassH1Vanishing` and
  `IdeleClassH2OrderBound` propositions. The last supplies both finiteness
  and divisibility of the order by the field extension degree.

For a cyclic extension, full idele range and agreement of the regular
invariant on quotient images give surjectivity onto the degree denominator
subgroup. The cardinality bound for the whole `H²` also bounds its regular
subgroup. Since the denominator subgroup has exactly the extension degree
as cardinality, this surjective map is bijective. Thus the regular invariant
is injective in the cyclic case.

For an arbitrary extension `E/F`, the proof chooses the published cyclic
auxiliary tower of degree `[E:F]`. Its auxiliary extension over `F` is cyclic,
as is its overfield over `E`. The preceding argument supplies the auxiliary
range and upper injectivity. The regular invariant's inflation and
restriction formulas provide the remaining compatibility hypotheses of
`regularIdeleClassInvariant_surjective_of_auxiliary`. Object descent and
`H¹` vanishing provide the actual inflation–restriction exactness used by
that result. This proves full denominator range on the regular subgroup
of the original extension.

The order bound now implies that the regular subgroup equals all of
`H²`. `assembledIdeleClassInvariantMaps` regards each actual class as a
regular class and applies the previously constructed regular invariant.
The implementation proves agreement on every regular class and, in
particular, on every image of actual idele cohomology. The same finite
cardinality argument proves injectivity; regular surjectivity and the
group-order annihilation result prove that its range is exactly the
degree denominator subgroup.

Finally, every class is regular, so the regular invariant's inflation
and restriction formulas apply directly to the full family. These are
the published `InvariantInflationOnClasses` and
`InvariantRestrictionOnClasses` conditions. Restriction allows a
nonnormal intermediate field.

The module does not construct the supplied idele family from local
invariants, discharge any of its laws or cyclic range, prove the three
arithmetic input propositions, or establish the finite-place local
compatibility condition. In particular its image and tower laws alone
do not assert `IsGlobalInvariant`.
