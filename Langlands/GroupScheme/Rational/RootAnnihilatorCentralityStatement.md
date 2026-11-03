# Root annihilation and central cocharacters

This is an internal structural reduction for the actual group schemes, root weights, and integral lattices already in the Library. The proposed `RootAnnihilatorCentralityStatement` says that, for a split torus mapping to a smooth connected affine group over any field, an integral cocharacter pairing to zero with every actual relative root is central on all test schemes. It retains arbitrary universe and rank zero and does not require reductivity or maximality.

The implemented zero-weight lemma is unconditional: split-torus weight decomposition spans the actual Lie algebra. Every nonzero summand either has weight zero already or has a relative-root character, whose restriction to the cocharacter is zero by the integral pairing hypothesis. Thus the cocharacter's zero weight space is the entire Lie algebra.

The centrality equivalences unfold the all-refinement centralizer and the functorial center. For a cocharacter, the published equality of its torus and dynamic centralizers gives the dynamic version.

The full centrality proposition remains a statement. The intended reduction uses the separately stated dynamic centralizer tangent description, smoothness, and equality for smooth closed subgroups with full Lie algebra. Their independent proof tasks remain necessary.
