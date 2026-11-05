# The actual unramified specialization of Henselian quasi-splitness

This internal proposition isolates the specialization from
`Langlands.GroupScheme.HenselianDiscreteQuasiSplitStatement` to
`Langlands.Geometry.Building.UnramifiedQuasiSplitStatement`, at the same
arbitrary universe `u`. It is a statement of the implication, not a proof of
either quasi-splitness assertion.

The premise is the universal theorem for fields carrying a surjective valuation
to `WithZero (Multiplicative ℤ)`, with Henselian valuation ring and algebraically
closed actual residue field. The conclusion retains precisely the original
nonarchimedean local-field assumptions on `F` and asserts quasi-splitness of every
connected reductive group over the actual published `UnramifiedClosure F`.
There are no additional field, group, model or descent hypotheses in the
conclusion.

The intended proof uses `MaximalUnramified.valuation F` and its published
surjectivity. The equality `MaximalUnramified.valuationSubring_eq F` identifies its
valuation ring with `LocalGalois.Separable.fixedFieldIntegers F` in the same field.
The existing Henselianity and algebraic-closure theorems for that ring and its
actual residue field then supply the generic theorem's premises. This
specialization neither proves the generic theorem nor establishes sharp torus
conjugacy.

The provenance is an internal arithmetic adapter between the two named
statements. Their mathematical source is Kaletha–Prasad, *Bruhat–Tits Theory: A
New Approach* (2023), Corollaries 2.3.7–2.3.8, printed p.81/PDF p.112, with the
Henselian discrete-field convention on printed p.80/PDF p.111. The 2024
corrections, Section 2.6, PDF pp.24–25, add Henselian/perfect-residue assumptions
for the later valued-group discussion and do not alter these Section 2.3 results.
