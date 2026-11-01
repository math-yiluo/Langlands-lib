# Injective original maps give surjective nondegenerate dual pullbacks

`Langlands.Algebra.nonUnitalModuleDualInjectiveSurjectiveStatement` proves
exactly the closed published proposition
`NonUnitalModuleDualInjectiveSurjectiveStatement.{uA,uM,uN}`. Its algebra,
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

The proof applies `NonUnitalModuleDual.pullback_surjective_of_injective`
from the accompanying `NonUnitalModuleDualMapExactnessProof` module. This
lemma extends a functional across the injective complex-linear map using
Mathlib's ordinary algebraic dual extension, then projects the extension
with an original idempotent fixing the original functional. The projection
belongs to the actual nondegenerate dual subtype, and intertwining makes
its actual published pullback the desired functional. The accompanying
Markdown explains this implemented route and its difference from Renard's
fixed-part proof.

The named full-dual actions and canonical recovered complex scalar
structures are those in the unchanged target. No finite-dimensionality,
unital-action, nontriviality, fixed-part equivalence or exactness-certificate
premise is introduced. Zero algebras and zero modules are included.
Complete unapplied examples retain arbitrary universes and unequal
specializations in both directions.
