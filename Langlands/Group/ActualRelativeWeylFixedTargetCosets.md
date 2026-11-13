# Fixed-target selected minimal transporters

This internal specialization of the actual transporter embedding supports the
Hom-dimension argument in Renard, *Représentations des groupes réductifs
p-adiques* (9 July 2026), VI.5.4, printed pp.173–174 / PDF pp.179–180. It uses
the source-coset convention of V.4.3–V.4.4, printed p.119 / PDF p.125.

Fix the source and target members `L I`, `L J` of the actual subgroup family.
Let `S` be any set of actual Weyl classes, with the explicit premise that each
member has a normalizer lift carrying the literal source onto the literal
target by forward conjugation. No invariance of `S` under changing lifts or
multiplication is assumed.

`fixedTargetTransporterSelection` restricts the existing lift-dependent
selection interface to that target and to lifts whose Weyl class lies in `S`.
`actualTransporterSourceCosets_fixedTarget` identifies its source-coset image
with the literal image of `S`. Both inclusions retain the same representative.
`fixedTargetMinimalTransporterEmbedding` retains the Weyl class and adds the
fixed target label, embedding the subtype of minimal members of `S` into the
existing type of selected minimal actual transporters.

`card_fixedTargetMinimalTransporters_le_sourceCosets` composes this embedding
with the published actual source-coset embedding and then takes cardinalities. Its hypotheses are a finite
actual Weyl group, containment of the full centralizer in each subgroup,
injectivity of the literal subgroup family, and the exact identification of
each Levi Weyl image with its standard Coxeter subgroup. These are precisely
the hypotheses of the existing embedding. The result counts the minimal
selected classes by the exact source-coset image of `S`.

This is a finite group-theoretic comparison. It does not assert any
representation-theoretic Hom bound.
