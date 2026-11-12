# Finite Artin symbols and norms through arbitrary intermediate fields

This module derives a finite norm square for the published arithmetic carry
symbol from the published norm law for standalone geometric Weil reciprocity.
Its provenance is internal: it composes the existing actual reciprocity,
finite Galois restriction, and determinant norm constructions.

Fix a prime `p`, p-adic fields `F` and `E` with carriers in an arbitrary common
universe `u`, and a field `D : Type u`. The tower has the supplied algebras
`F → E`, `F → D`, and `E → D`, compatible in the sense of
`IsScalarTower F.Carrier E.Carrier D`. All three relative extensions are
finite-dimensional. The top field `D` is Galois over each of `F` and `E`.
The theorem also assumes compatibility of `F → E` with the supplied
`Padic p` algebras. It does not assume that `E/F` is normal.

`FiniteArtinSymbol.ArtinNormCompatibility` is the Prop-valued equality of the
following homomorphisms from `E.Carrierˣ` to
`Abelianization Gal(D/F.Carrier)`:

- first apply `abelianizedArtinSymbol E D`, then apply the abelianization of
  the actual `AlgEquiv.restrictScalarsHom F.Carrier`;
- first apply `normUnits F.Carrier E.Carrier`, then apply
  `abelianizedArtinSymbol F D`.

The property itself only needs the algebraic tower data used to form these
maps. The theorem `artinNormCompatibility` proves it under all of the
compatible p-adic tower hypotheses above. Its pointwise form is
`abelianizedArtinSymbol_norm`. Here `normUnits` is the existing determinant
norm, and the symbol is the existing character-defined arithmetic carry
symbol with values in the actual finite Galois abelianization.

The auxiliary theorem
`FiniteQuotientTransport.closureFiniteRestriction_reciprocityUnits` fixes a
finite Galois field `D/F` embedded in `AlgebraicClosure F.Carrier` by compatible
algebra and scalar-tower instances. For any standalone reciprocity candidate
`e` satisfying the geometric Weil reciprocity relation and any actual Weil
element `w`, it identifies the abelianized finite restriction of
`localProjection F w` with the inverse of the arithmetic symbol of
`reciprocityUnits F e w`. The proof specializes the published
`closureFiniteAbelianRestriction_geometric` theorem and cancels `e.symm ∘ e`.

For the norm square, the proof chooses an `E`-algebra embedding of `D` in
`AlgebraicClosure E.Carrier`. It transports this embedding through the inverse
of the chosen closure isomorphism `extensionClosureEquiv F E f`, where `f`
is the supplied inclusion `F →ₐ[Padic p] E`. The defining equivariance of
`extensionGaloisMap` then identifies its finite restriction with restriction
of scalars on `Gal(D/E.Carrier)`. This step uses normality of the top field
over each base, not normality of the middle field over the bottom field.

Next the proof chooses a Weil representative whose canonical standalone
geometric reciprocity value is `a⁻¹`. The published
`reciprocityUnits_extensionWeilMap` theorem identifies the reciprocity value
of its image with the norm of `a⁻¹`. The algebra structure induced by `f`
is identified with the supplied algebra structure using `Algebra.algebra_ext`,
so this is precisely the existing `normUnits`. Applying the auxiliary
finite restriction formula over both bases and cancelling the inverses
gives `abelianizedArtinSymbol_norm`. Extensionality proves the equality of
homomorphisms.

This finite norm result is a prerequisite for the common-closure reciprocity
construction. It does not prove the finite Tate cup comparison, finite
transfer compatibility, or the full common-closure reciprocity existence
statement.
