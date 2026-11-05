# The Hopf structure on cocommutative coinvariants

The first two sections prove general Hopf identities: the antipode reverses comultiplication, and a bialgebra map commutes with antipodes. Both follow from uniqueness of convolution inverses, expressed through finite comultiplication representations. These identities do not require cocommutativity.

For a bialgebra map π: A → B between commutative Hopf algebras, the later construction equips the coinvariant subalgebra `hopfKer π` with a Hopf structure when A is cocommutative and A, B, and the coinvariants are flat over the commutative base ring R. Coassociativity shows that Δ of a coinvariant is annihilated by the coaction difference on the second factor. Cocommutativity gives the first-factor condition. Tensor exactness and flatness then place Δ in the image of the tensor square of the subalgebra inclusion. Injectivity of that inclusion defines the restricted comultiplication and reflects its laws, with analogous checks on the tensor cube. The counit and antipode restrict from A, the result is cocommutative, and `hopfKerVal` is an injective bialgebra homomorphism to A.

The general faithful-flatness proof imports this file for the unrestricted antipode/comultiplication identity. Its final conclusion does not assume the cocommutativity or flatness hypotheses of this separate coinvariant-structure construction.

Source: `Definitions/Def_HopfAlgebra_HopfKerHopf.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `4f27418c5f0ccb68de9bb7150b61154d9bb7c50ccf8c0fc8eece0b3895eaf6b1`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports are prefixed and finite source-project elaboration settings are supplied. Tensor inductions explicitly select `TensorProduct.induction_on` to retain their zero, pure-tensor and addition cases with the current Mathlib API.
