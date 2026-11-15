# Proof of the descent of smooth factorizations from a localization

`Langlands.CommutativeAlgebra.Popescu.localizationStandardDescent` proves
`Langlands.CommutativeAlgebra.Popescu.LocalizationStandardDescentStatement.{u}` for every
universe `u`. This is the strictly standard form of Stacks Project, *Smoothing ring maps*,
Lemma 8.3 (tag 07F4).

The proof is one line. It applies `localizationStandardDescent_of` (module
`Langlands.CommutativeAlgebra.Popescu.LocalizationStandardDescentAssembly`), which derives
the statement from `StandardSmoothRetractStatement` (Stacks Lemma 3.4, tag 07CH), to the
published Library proof
`Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetract.standardSmoothRetract` of that
statement (module `Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetractProof`). The
assembly module's Markdown describes the argument. No hypotheses are added, and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
