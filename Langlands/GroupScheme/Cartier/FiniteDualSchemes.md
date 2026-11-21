# Finite dual spectra and their maps

`schemeDual` takes the actual affine coordinate Hopf algebra of a commutative group scheme finite, flat and locally of finite presentation over an affine base. Those hypotheses give finite projective coordinates. The spectrum of the convolution dual is therefore again a commutative group scheme with the same three geometric properties.

`AffineHopfMorphism.pullback` first uses the canonical affine Hopf-coordinate isomorphisms and then takes the corresponding bialgebra map. `schemeDualMap` transposes that map and takes its relative spectrum. Thus a map from \(G\) to \(H\) gives an actual map from the finite dual of \(H\) to the finite dual of \(G\). The verified identities and reversed compositions permit these maps to be used in torsion diagrams.

The construction derives the spectrum maps from the dual algebra and evaluation of Demazure and Gabriel, *Groupes algébriques*, Tome I (1970), Chapter II, §1, no. 2, 2.10, printed pp. 156–158 (PDF pp. 186–188). The application is to the Cartier dual factor of the split polarized object in Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321).
