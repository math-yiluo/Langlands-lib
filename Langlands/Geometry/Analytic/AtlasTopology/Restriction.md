# Restriction of atlas nets

This module constructs restriction infrastructure for the actual induced topology on a member of a net. The source is V. Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §1.1, definitions of quasinet and net on printed pp. 13–14 (registered source `berkovich-1993-etale-cohomology`, PDF pp. 10–11). The explicit homeomorphism and the general restriction lemma are derived infrastructure, not separately attributed source statements.

`restrictionInterHomeomorph` identifies the subspace `U ∩ V` of the original space with the intersection of the inverse images of `U` and `V` inside a subspace `S`, assuming `U ⊆ S`. Both maps retain the underlying point. Their continuity follows by composing the actual subtype inclusions.

`restrictionInterHomeomorph_imageFamily` proves that the family of original members contained in `U ∩ V` corresponds exactly to the family obtained by first restricting to `S` and then to that intersection. In both directions the proof retains the same original member; containment is transferred by the subtype inclusion.

`IsNet.restrict` uses this equality and the published homeomorphism transport of quasinets to transfer the pairwise intersection condition. Its hypothesis explicitly supplies the ambient quasinet on `S`. `IsNet.restrict_member` discharges that hypothesis for an actual member of the original family: its inverse image is the entire subspace, which gives a singleton quasinet witness. There is no ambient Hausdorffness or openness assumption.
