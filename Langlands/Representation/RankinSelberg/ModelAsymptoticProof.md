# Transport of Whittaker expansions to coefficient models

`Langlands.RankinSelberg.modelAsymptoticTransfer` proves exactly
`ModelAsymptoticTransferStatement`, at independent universes `uF` and `uV`.
The theorem is conditional on `WhittakerTypeAsymptoticStatement`. It does
not prove that analytic prerequisite or the equal-rank analytic theorem.

For the standard character and canonical topology, the proof first rewrites
the additive character of the sum of first-superdiagonal entries as the
product of its values. This identifies the functional equation in the
canonical expansion target with membership in `glFunctionals`.

The linear equivalence between the functional space and the complex scalars
in `IsOfWhittakerType` supplies a nonzero functional: the inverse image of
`1`. Injectivity of that equivalence shows that every equivariant functional
is a scalar multiple of the chosen one. Together with the admissibility and
finite generation already present in `IsOfWhittakerType`, these facts allow
application of the assumed canonical expansion. Its finite set is selected
before the functional and vector. Surjectivity of `modelMap` then gives a
representing vector for each element of the actual coefficient-model image.
The two diagonal constructors agree definitionally, so the expansion
identity applies directly to that image function.

For an arbitrary supplied `TopologicalData`, the published theorem
`topology_eq_canonicalModule` identifies its topology with the canonical
one. Rewriting this equality transports the entire proposition, including
continuity, smoothness, and the Schwartz–Bruhat coefficient types. The
inverse-character case applies the standard case to `ψ.scale (-1)` and uses
`standardCharacter_scale_neg_one`. The existing scale construction preserves
nontriviality and continuity. No irreducibility or nonzero-model-functional
assumption is added; the conclusion includes zero functionals as well.

This is an internal transport proof. The analytic source content remains in
the explicit antecedent and is documented in
`ModelAsymptoticStatement.md` and `Whittaker/AsymptoticStatement.md`:
JPS (1979), Proposition 2.2 and Remark 2.2.5, printed pages 181–183;
JPSS (1983), section 2.5, printed pages 388–389, and the proof of
Theorem 2.7 on pages 391–392. The implemented proof uses only the Library
interfaces just described, rather than repeating the source's analytic
argument.

Sources: `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`;
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
