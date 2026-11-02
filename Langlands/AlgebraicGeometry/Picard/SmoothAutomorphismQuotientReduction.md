# Reduction of the Picard atlas theorem to the generic smooth quotient

This internal construction reduces the actual Picard atlas theorem to the
single explicit input `AlgebraicSpace.SmoothRelationQuotientStatement.{u}`.
It uses the published double-quotient construction, source descent of
smoothness and local surjectivity of an actual smooth Picard presentation.
It does not prove the generic quotient proposition or provide an
unconditional proof of `SmoothAutomorphismEtaleAtlasStatement`.

The schemes `S` and `X`, their morphism `f`, and the universe `u` are arbitrary.
The other inputs are precisely
`PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas f` and
`PicardGroupoid.HasSmoothRelativeAutomorphismSchemes f`. They refer to the
actual line-bundle pseudofunctor and its full point-fibre and relative
automorphism presheaves. No restriction is placed on the scheme tests or
on the sections of the sheaf.

`smoothAutomorphism_picardProperties_of_smoothRelationQuotient` extracts
an actual scheme `U` and family `L` from the atlas hypothesis, retaining
both local finite type of `U` over `S` and the smooth surjective presentation
by `L`. The published
`smooth_of_smooth_of_surjective_of_smooth_comp` supplies the source-descent
input of `smoothDoubleQuotient_picardProperties`: its smoothness and
surjectivity premises are supplied explicitly, and the theorem gives
smoothness of the descended scheme map. The published
`etaleFamilyMap_isLocallySurjective f L hL` supplies the other formerly
explicit input on the entire big etale site.

The double quotient then gives fppf sheafness, a scheme-representable
diagonal, and an actual etale surjective scheme atlas locally of finite
type over `S` for `RelativePicard.etaleClassSheafPresheaf f`. Both uses of
the generic quotient theorem remain conditional on the same supplied
`hQuot`. The published comparison in that construction identifies the
entire quotient with ordinary etale Picard classes, including sections
with no global line-bundle representative.

`smoothAutomorphismQuotientPicardSpace` packages these properties into an
algebraic space whose underlying presheaf is definitionally the original
ordinary Picard presheaf. Its presheaf lemma is proved by reflexivity.
The preceding properties lemma retains the local finite type conclusion,
which the algebraic-space structure itself does not record.

`smoothAutomorphismEtaleAtlas_of_smoothRelationQuotient` forgets the fppf
sheaf property and obtains the exact published Picard target from the
generic quotient proposition. It accepts the target's stack hypothesis;
the proof does not use it because the presentation, local-surjectivity
and double-quotient results already provide all required properties.
The generic quotient proposition is still a hypothesis of this theorem.

The provenance is the internal composition of these published interfaces.
This supporting construction leaves one substantial prerequisite open:
an independently accepted and published proof of the generic
smooth-relation quotient theorem. It is not a completion contribution for
the host Picard proof task.
