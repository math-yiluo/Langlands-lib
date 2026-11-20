# Nilpotent rigidity of actual local quasi-isogenies

`localQuasiIsogenyNilpotentRigidity` proves `LocalQuasiIsogenyNilpotentRigidityStatement`, the affine coordinated case of the rigidity in Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), §2, p. 52, equation (2.1) and the paragraph following Definition 2.8, where it is attributed to Drinfeld.

The proof first works with a surjective coefficient map with nilpotent kernel and surjective map on spectra. On each basic open the actual structure-sheaf pullback has nilpotent kernel. Integral Hom pullback is injective there, and flat scalar extension preserves this injectivity on rational tensors. Local representatives for the sheafification and refinement by basic opens then give injectivity on rational sections over any open.

For existence, start with the given local quasi-isogeny on the inverse-image open. Around each point choose a basic open on which a power of the scalar times the given section is an integral isogeny. The integral lifting lemma and the scalar-composites criterion give an actual isogeny upstairs whose reduction is a further scalar power times this numerator. Dividing the lift by the combined power gives a rational section on the basic open with the required reduction and local scalar-isogeny condition.

The local sections agree on overlaps by injectivity of pullback. Glue them using the actual rational Hom sheaf and descend the local scalar-isogeny condition along the cover. The glued section reduces to the given one by equality on the inverse-image cover. Injectivity on rational sections gives uniqueness of the lift.

For the exact statement, apply this construction to the quotient map. A nilpotent ideal is contained in the nilradical, which gives surjectivity on spectra. The prime is nonzero in the lifted rational field, and that field is flat over the integers by torsion-freeness.
