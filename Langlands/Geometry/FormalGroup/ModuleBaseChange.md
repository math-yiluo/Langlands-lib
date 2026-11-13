# Base change of formal module isomorphisms and quasi-isogenies

Coefficient extension of integral O-linear formal homomorphisms preserves
identity and composition. `Iso.refl`, `symm` and `trans` supply the
isomorphism operations, and `Iso.map` extends both inverse maps along an
O-algebra homomorphism.

Two formal O-modules with the same addition series and scalar-action series
are canonically isomorphic by the identity coordinate map
(`Iso.ofIdenticalCoordinates`). Applying coefficient-mapping identities
constructs `ModuleLaw.mapIdIso` and `mapCompIso`: extending coefficients
along the identity, or along two successive maps, gives the original
module, or the module extended along their composite, up to these
specified isomorphisms. Both comparison maps use the identity coordinate
map.

On rational Hom, coefficient extension takes `a ⊗ f` to `a ⊗ f.map φ`.
Tensor induction proves that it preserves composition, and the pure
tensor formula proves preservation of identity and of integral
rationalization. Consequently `QuasiIsogeny.map` extends both the
rational homomorphism and its inverse. It preserves identity, inverse,
composition and the quasi-isogenies induced by integral isomorphisms.
`QuasiIsogeny.ext_hom` proves that equality is detected by the rational
homomorphism: the inverse is forced by its inverse equation.

This is derived algebraic infrastructure for the finite-coordinate
formal O-modules and rational Hom in Drinfeld, *Coverings of p-adic
Symmetric Regions* (1976), §1, printed p.108, and §2 A, opening
paragraph, printed p.109. The actual coefficient and tensor maps are
constructed from those in the preceding modules; no separate
representability or rigidity assertion is assumed. Heights,
nilpotent-thickening rigidity and locally glued formal groups remain
subsequent work.
