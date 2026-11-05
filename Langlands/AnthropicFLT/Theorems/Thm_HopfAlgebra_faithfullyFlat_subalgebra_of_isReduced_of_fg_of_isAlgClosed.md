# Faithful flatness over a reduced finite Hopf subalgebra — theorem interface

Let H be a finite type commutative Hopf algebra over an algebraically closed field k. If K is a finitely generated k-subalgebra stable under comultiplication and antipode, and K is reduced, then H is faithfully flat over K. Reducedness of H is not required.

The theorem `HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed` applies the companion `P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.md):

`TakK` restricts the Hopf structure to K. Tensor inclusions are injective over the field, so the restricted comultiplication and all its laws can be verified after inclusion into H. For existence of a flat localization, choose a minimal prime of reduced K and a prime of H above it; localization of K there is a field. The flat locus in Spec H is open by the imported local-flatness theorem. Translation by k-points transports flatness between all maximal primes, including the corresponding automorphism of K. A nonempty open subset invariant on maximal points is the whole Jacobson spectrum. Localization at all maximal ideals now proves flatness of H over K. Finally apply the injective-flat Hopf-map theorem to obtain faithfulness.

Source: `Theorems/Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `bc96bafbd4536530f6699167cfb51b850ba5469dd340e4679b6c97b90412ca14`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
