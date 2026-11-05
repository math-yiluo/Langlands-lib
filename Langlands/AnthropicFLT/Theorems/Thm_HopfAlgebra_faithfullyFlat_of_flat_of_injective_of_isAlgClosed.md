# Injective flat maps of finite type Hopf algebras are faithfully flat — theorem interface

Over an algebraically closed field k, let K and H be finite type commutative Hopf algebras with a compatible algebra structure K → H preserving comultiplication and counit. If this map is injective and H is flat over K, then H is faithfully flat over K. The Hopf algebras need not be reduced.

The theorem `HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed` applies the companion `P2MW.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.md):

The image U of Spec H in Spec K is open because the map is flat and finitely presented over the Noetherian ring K, and dense because the algebra map is injective. Closed points are k-points by the finite type Nullstellensatz, and membership in U is equivalent to lifting a k-point to H. Such lifts are closed under convolution. For a point z, consider the inverse-translation open set V for z. It is nonempty since the identity lifts. Density makes V intersect U, and the Jacobson property supplies a k-point in the intersection. Multiplying its two lifts produces a lift of z. Thus all maximal primes lie in U; the spectrum criterion makes U the whole space. Flatness and surjectivity of prime-spectrum comap then give faithful flatness.

Source: `Theorems/Thm_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `ea9a3c0411da716fb4c69d5bb93864ef8641453ac4d3d2731113bca1a048d60a`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
