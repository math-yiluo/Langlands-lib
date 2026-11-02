# Relative morphism properties of presheaves

The etale composition and Yoneda-image results reuse `IsEtale.comp` and
`isEtale_map` from `EtaleEquivalenceRelationPresentation`.

Additional internal helpers:

- composition, and composition with isomorphisms, of relative etale maps and relative open
  immersions (`IsEtale.comp_iso`, `IsEtale.iso_comp`,
  `IsOpenImmersion.comp'`, `IsOpenImmersion.iso_comp`, `IsOpenImmersion.comp_iso`);
- `isAffineOpen_range`: the range of an open immersion from an affine scheme is an affine
  open subfunctor;
- `dense_iInter_of_isOpen_finite`: a finite intersection of dense open sets is dense.
