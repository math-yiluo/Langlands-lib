# Epimorphic images of saturated Tits systems

This internal algebraic transport implements the quotient step of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 1.4.12(1), printed pages 51–52
(PDF pages 82–83). An epimorphism `f : G →* G'` has kernel contained in `B ∩ N`.
The target projection `π' : N.map f →* W` agrees with the source projection on
every source normalizer element. The groups have three independent universes.

`IsTitsSystem.map` transports all Tits axioms to the images with the same Weyl
group and simple reflections. `TitsSystem.IsSaturated.map` transports the corrected
saturation equality, the intersection of all normalizer conjugates of the Borel
being `B ∩ N`. The general transport accepts an explicit target projection.
`TitsSystem.imageProjection` constructs one canonically whenever the source Weyl
projection kills the kernel on the normalizer. `imageProjection_apply` specifies
it on every image representative. `IsTitsSystem.ker_subgroupMap_le` derives the
needed kernel containment from the Borel-kernel hypothesis, and
`IsTitsSystem.map_imageProjection` transports to this canonical projection. The
construction descends the source homomorphism through the surjective normalizer
image map using Mathlib's `MonoidHom.liftOfSurjective`. This unit supplies no
Bruhat–Tits geometric inputs.

The proof first identifies image Bruhat cells by lifting their three factors.
When the kernel lies in the Borel, subgroup membership and Bruhat-cell membership
can be checked before applying the homomorphism. These facts transport the kernel
and multiplication axioms and preserve the witness to the conjugation axiom.
Surjectivity transports generation. For saturation, injectivity of subgroup
preimage reduces the equality to the original group; conjugate membership is
rewritten as inverse conjugation, and every image normalizer representative lifts.
This is a direct group-theoretic proof of the source lemma's quotient argument.
