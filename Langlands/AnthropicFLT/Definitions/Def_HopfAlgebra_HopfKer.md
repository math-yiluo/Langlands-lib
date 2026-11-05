# Coaction, coinvariants and the canonical Hopf map

For a bialgebra homomorphism π: A → B between commutative R-bialgebras, `coaction π` is (id tensor π) composed with Δ. `hopfKer π` is its equalizer with a ↦ a tensor 1; thus it is the subalgebra of coinvariants. `canAlgHom π`, and its underlying linear map `canMap π`, send a tensor a' to (a tensor 1) times the coaction of a'. Their balancing relation over a coinvariant element h is proved directly.

`balancingRelations π` consists of (a h) tensor a' − a tensor (h a') for coinvariant h. Span induction shows that the canonical map kills these relations. `IsHopfGalois π` is the proposition that the canonical map is surjective and every element of its kernel belongs to their R-linear span. This is an algebraic coinvariant construction; it is not a definition of the scheme-theoretic kernel used in the final group-scheme statement.

Source: `Definitions/Def_HopfAlgebra_HopfKer.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `97ebc95aa2b649956109cf34f165825d0c4613522c8c88a365f13b914727121d`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports are prefixed and finite source-project elaboration settings are supplied.
