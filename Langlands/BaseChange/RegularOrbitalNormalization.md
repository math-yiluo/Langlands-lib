# Normalized measures on regular orbits

Let `F` be a nonarchimedean local field and `E` a cyclic `F`-algebra with its module topology. Give the two general linear groups their Borel measurable spaces and arbitrary ambient Haar measures. The ordinary locus consists of elements with separable characteristic polynomial. The twisted locus consists of elements with a norm associate in the ordinary locus. In characteristic zero these are the regular loci of Henniart–Lemaire I.2.3. In positive characteristic these are the regular semisimple subloci described there.

For each element on these loci the module chooses Haar measure on its centralizer with mass one on the largest compact open subgroup and a compatible measure on the left quotient. The chosen centralizer measures are associated at every associated pair in the two loci.

The centralizer is commutative, so left invariance of its normalized Haar measure gives right invariance. On the twisted side the proof transports commutativity through the continuous norm centralizer equivalence. The ambient general linear groups have right-invariant Haar measures, and finite-dimensional coordinates give the topology used by the measure results. The measure on the left quotient exists by the Library's Weil formula for a closed subgroup.

For a witness `x` of the norm association, the norm centralizer equivalence takes `t` to `x * baseChange F E n t * x⁻¹`. It pushes normalized ordinary Haar to normalized twisted Haar by preservation of the largest compact open subgroup. Pushing both measures into the ambient extended group and using this formula proves the Library's `IsAssociatedMeasure`.

The loci follow the separability condition in Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011), I.2.3, printed pp. 13–14, PDF pp. 21–22. The internal construction uses the associated-measure convention of I.2.5, printed p. 17, PDF p. 25. The volume-one prescription is in I.2.7, printed p. 19, PDF p. 27. The Remarque of I.2.7, printed pp. 20–21, PDF pp. 28–29, gives association for this normalization on printed p. 21.
