# Strict character contraction on the actual split-torus section

This derived module converts a closed norm bound on the strict intrinsic
uniformizer chamber of an actual split torus into a strict bound for each
nonunitary smooth character.

The common norm kernel of the actual split torus is compact, so a smooth
character has norm one on it. The intrinsic uniformizer-section theorem
represents every actual point modulo that kernel. Thus if the character
takes a value of norm different from one on the torus, it already has
`IsNonunitaryOnCA`, meaning that such a value occurs on the intrinsic
lattice section.

On that section, the algebraic character orders form an additive map to a
real vector space of functions on the character lattice. The given finite
chamber character set becomes a finite set of coordinate linear forms.
The existing chamber argument then applies: if a character of norm at most
one on the open chamber had norm one at an interior point, translating a
sufficiently large power of that point by any section element or its inverse
would force that element's norm to be one. This contradicts nonunitarity.

For the actual ordinary normalized standard Jacquet action, generalized
eigencharacters have open kernel because the action is smooth and the
unchanged component map is continuous. The final specialization combines
this with the actual strict-ray exponent bound. Original-coefficient Xi
control and polynomial Xi bounds on every strict component ray remain
explicit intermediate inputs; all structural contraction and smoothness
requirements are derived.

The contextual original source is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), Proposition III.2.2,
printed pp.265–266, and its use in VI.2.3, printed pp.299–300, source
`waldspurger-2003-plancherel`. The intrinsic-section specialization is derived
project content and leaves the chamber norm bound explicit.
