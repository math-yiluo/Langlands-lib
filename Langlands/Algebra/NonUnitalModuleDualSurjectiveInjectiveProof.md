# Surjective original maps give injective nondegenerate dual pullbacks

`Langlands.Algebra.nonUnitalModuleDualSurjectiveInjectiveStatement` proves
exactly the closed published proposition
`NonUnitalModuleDualSurjectiveInjectiveStatement.{uA,uM,uN}`. Its algebra,
source and target universes are independent; it has no unused third module
and adds no premise.

This is the endpoint consequence of Renard I.4.1, the exactness lemma on
printed page 23 / PDF page 29 of the French edition dated 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original conventions (PDF pages 11–13), scalar recovery (PDF page 20),
splitting (PDF page 25), and duality (PDF pages 28–29) were read directly.
The registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pages 1–2; its nearby corrections leave this exactness
assertion unchanged in the governing edition.

The proof applies `NonUnitalModuleDual.pullback_injective_of_surjective`
from the accompanying `NonUnitalModuleDualMapExactnessProof` module. Two
actual nondegenerate dual elements with equal pullbacks agree at f(m)
for every original m. Surjectivity supplies a preimage of every target
vector, so the two entire functionals agree. Extensionality of the actual
nondegenerate subtype gives equality. This argument needs neither full-dual
extension nor the separately owned fixed-part inverse or equivalence.

The named full-dual actions and canonical recovered complex scalar
structures are those in the unchanged target. No finite-dimensionality,
unital-action, nontriviality or exactness-certificate premise is introduced.
Zero algebras and zero modules are included. Complete unapplied examples
retain arbitrary universes and unequal specializations in both directions.
