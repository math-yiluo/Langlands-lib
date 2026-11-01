# Scheme adapters for discrete valuative specialization lifting

These are internal derived lemmas for the displayed-base discrete valuative closed-image proof. No additional geometric hypotheses enter the final statement.

`stalkSpecializes_essFiniteType` chooses an affine open containing the specialization point. Both points lie in it. The germ at the general point is a localization and hence essentially of finite type; its factorization through the specialization stalk map proves that map is essentially of finite type.

`specializationResidueMap_essFiniteType` composes this map with the essentially finite type stalk map of a locally finite type morphism and the surjective residue-field quotient. Its domain is the stalk at the prescribed specialization point and its codomain is the residue field at the prescribed source point.

`specializationResidueMap_commutes` identifies the composite map on spectra with the source residue-field map followed by the scheme morphism. If this stalk-to-field ring map is local, its spectrum map takes the field point to the stalk closed point. Evaluating that commutative identity shows that the two base points coincide; this is `specializationResidueMap_local_imp_eq`.
