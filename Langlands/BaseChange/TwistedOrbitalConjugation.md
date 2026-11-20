# Transport under twisted conjugation

For a topological group `G` and an endomorphism `θ`, write `δ' = x⁻¹ δ θ(x)`. Conjugation by `x⁻¹` identifies the twisted centralizer of `δ` with that of `δ'`. The homeomorphism of left quotients sends the coset of `a` to the coset of `x⁻¹ a`. It commutes with right translation and identifies the orbit integrands since twisted conjugation by `x` followed by `x⁻¹ a` is twisted conjugation by `a`.

`TwistedOrbitalConjugationStatement` uses the Borel measurable structures and right-invariant measures on the two centralizers, with the target measure given by pushforward of the source measure. The statement gives compatibility of the transported quotient measure with the fixed left-invariant ambient measure, along with integrability equivalence and orbital-integral equality for all complex-valued functions.

In `isCompatible_map_twistedConj`, pulling back the new subgroup average gives the old subgroup average applied to `a ↦ f (x⁻¹ a)`. The original Weil formula and left invariance of the ambient measure give the new formula. The homeomorphism also transports regularity, nonzeroness, right invariance and integrability of the average.

The theorem `twistedOrbitalIntegral_map_conj` uses the formula for the orbit integrand and changes variables along the quotient homeomorphism. It preserves integrability and the value of the Library's twisted orbital integral under transport of the quotient measure. These are derived lemmas for the conjugacy invariance used in Henniart–Lemaire (2011), I.2.7–I.2.8.
