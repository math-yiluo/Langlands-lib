# The glued abelian scheme of a rigid family of data

Helper module for Zariski gluing of ordinary polarized full-level data (used by `ModuliZariskiSheafOfRigidityProof`, which derives the Zariski sheaf property from rigidity).
Setting as in `ZariskiGluingScheme`: rigid data `c W` on the small opens `W` of an open
cover of `S`, with polarized isomorphisms `θ` between restrictions.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel`:

- `unitSection_eq_one_left`: `unitSection A = η[A.X].left`.
- `PolarizedIso.unitSection_overMap`: transition maps preserve unit sections,
  `unitSection c.abelian ≫ θ.overMap = b ≫ unitSection c'.abelian`.
- `abelianIsoOfUnit e he`: an isomorphism `e : A.X ≅ B.X` of the underlying schemes
  over the base of two abelian schemes, with `η[A.X] ≫ e.hom = η[B.X]`, is an
  isomorphism of abelian schemes (`hom` of it is `e.hom.left`). Both `e.hom` and `e.inv`
  are monoid morphisms by the Library's `pointedMorphismRigidity`, applied to the
  abelian source and to the smooth and proper target.

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing`:

- `glued`, `gluedι W`: the glued scheme (colimit of `gluingFunctor`) and the inclusion
  of the piece over `W`.
- `gluedUnit`: the unit sections `unitSection (c W).abelian ≫ gluedι W`, glued along
  the locally directed cover of `S` (`glueMorphismsOfLocallyDirected`, compatibility
  `unitSection_compat`). `gluedUnit_restrict`, `gluedUnit_toBase`: it restricts to the
  local unit sections and is a section of the glued structure map.
- `gluedOver`, `gluedSection`: the glued scheme over `S` and its unit as a point.
- `localIso W`: the pullback of `gluedOver` along `W.ι` is `(c W).abelian.X`
  (`gluingData_isPullback`).
- `exists_gluedAbelian`: there are an abelian scheme `B` over `S` and an isomorphism
  `gluedOver ≅ B.X` taking the glued unit to the unit of `B`. This is the Library's
  `abelianSchemeStructureOfOpenCover` (proof of `AbelianSchemeStructureOfOpenCoverStatement`)
  applied to the cover `subCover hU` and the local abelian schemes `(c W).abelian`.
- `gluedAbelian`, `gluedIso`, `gluedIso_unit`, `unitSection_gluedIso_inv`: a choice of
  such `B`, with its isomorphism and unit compatibility.
- `restrictOverIso W`, `restrictOverIso_unit W`, `restrictIso W`: the isomorphism
  `(baseChange W.ι).obj B ≅ (c W).abelian` of abelian schemes over `W`, built from
  `gluedIso` and `localIso` and made a homomorphism by `abelianIsoOfUnit`.
- `hom_restrictIso_gluedι`: `hom (restrictIso W).hom ≫ gluedι W` is the first projection
  followed by `gluedIso.inv`.

## Proofs

Unit compatibilities are checked after composing with the monomorphism `gluedι W` (an
open immersion), using `unitSection_baseChange_fst`, `gluedUnit_restrict` and the
projection formula `IsPullback.isoPullback_inv_fst`.

## Provenance

The abelian-scheme structure on a scheme over `S` that is locally an abelian scheme is
the Library's `AbelianSchemeStructureOfOpenCoverStatement`. Rigidity of pointed
morphisms, the Library's `PointedMorphismRigidity` (see its Markdown for its source in
K.-W. Lan's thesis, Corollary 1.3.1.6), makes the comparison isomorphisms
homomorphisms. The gluing itself is internal.
