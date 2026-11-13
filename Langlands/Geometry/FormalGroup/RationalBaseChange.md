# Coefficient extension and inverse uniqueness for formal modules

For finite-coordinate formal O-modules over a commutative O-algebra R,
this module reuses coefficient extension from `ModuleBaseChange` and its
coherence laws from `CoefficientCoherence`. There is one implementation of
integral `Iso.map` and rational `QuasiIsogeny.map`: both extend the actual
forward and inverse formal maps along an O-algebra homomorphism R → S.
The common implementation proves preservation of identity, composition,
inverses and integral rationalization by coefficient substitution and
induction on the actual tensor-product rational Hom. No flatness
hypothesis on the coefficient map is needed.

The additional lemma `ModuleLaw.Iso.inv_unique` proves that a left inverse
of the forward map of an actual integral isomorphism equals its inverse.
The proof inserts the identity as the product of the forward and inverse
maps, reassociates and applies the assumed left-inverse equation.
`Iso.ext` and `QuasiIsogeny.ext` are compatibility names for the common
`ext_hom` lemmas: forward-map equality forces equality of both fields.

`Iso.map_refl`, `map_symm` and `map_trans` prove that integral coefficient
extension preserves identity, inverse and composition. The first and
third follow from forward-map extensionality and the corresponding
integral Hom coefficient laws; the inverse formula is definitional.
The imported `QuasiIsogeny.map_refl`, `map_symm`, `map_trans` and
`map_ofIso` provide the analogous rational compatibilities.

This is derived algebraic infrastructure for the quasi-isogenies of
Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 A, opening
paragraph, printed p.109 (PDF page 3), literature
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source defines quasi-isogenies as invertible elements of
Hom(M,N) ⊗_O F. The construction uses F ⊗_O Hom(M,N), related to the
source's order by `RationalHom.sourceTensorEquiv`. The present lemmas
follow from this algebraic definition; they do not assert the
nilpotent-thickening rigidity in the following source sentence. Heights,
locally glued formal groups and representability remain subsequent work.
