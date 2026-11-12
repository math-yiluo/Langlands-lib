# Actual norm-one rational quotients under Weil comparison

Author: Worker 82.

`LeftCosetSpace.congrHomeomorph` descends a continuous group equivalence to
left homogeneous quotient spaces when it maps the specified subgroup onto
the specified subgroup. It uses the existing quotient types and topologies;
normality and discreteness are not needed. The equivalence preserves the
left equivalence relation, and the quotient universal property proves
continuity of both directions. The formula on representatives is definitional.

For actual Weil restriction, `normOnePointsEquiv` restricts the fixed
`adelicPointsEquiv F L G` to the existing norm-one subgroups. It explicitly
assumes that this canonical map is a homeomorphism and that its image of
the lower norm-one subgroup is the upper norm-one subgroup. It does not
replace either topology by a transported topology.

With the additional exact principal-point square,
`normOnePointsEquiv_rational` proves the square for the restricted map and
`map_rationalNormOneSubgroup` proves equality of its principal subgroup
image. Applying the quotient construction gives
`normOneRationalQuotientHomeomorph`, with the stated representative formula.
`hasCompactNormOneRationalCover_iff` transfers compact principal covers in
both directions by the published equivalence of compact quotient and
compact representatives for finite-type affine groups.

These are internal conditional constructions for the use of Springer,
*Reduction theory over global fields* (1994), §1.4 and §3.1(a)–(b), printed
pp.208–209 and 214 (PDF pp.2–3 and 8). The registered source is
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, file
`literature/Reduction theory over global fields (Springer, 1994).pdf`.
No errata note exists. All three comparison hypotheses are still unproved
here; they are precisely the local conclusions requested by the published
`NormOneComparisonStatement`. No closed-immersion unit, scalar-extension
quotient embedding, compactness over either field, or general central-split
compactness theorem is proved by this module.
