# The inducing parabolic in its standard family

Module `Langlands.Global.AdelicEisensteinFamilyStandardSource` replaces the inducing parabolic
`P` of the family comparison (module `Langlands.Global.AdelicEisensteinFamilyRegularComparison`)
by the standard parabolic of the same root data.

## Definitions and auxiliary results

For a root presentation `r` of `(p, l, a)` (`ParabolicRootPresentation`) of a connected
reductive `G` (`hG`):

- `ParabolicRootPresentation.standardFamily hG r` is the standard parabolic family
  `StandardParabolicFamily.ofMaximalSplitTorus hG r.data.i r.isCompatible.maximalSplit
  r.data.ν r.isCompatible.generic` of the maximal split torus and generic cocharacter of `r`.
- `ParabolicRootPresentation.standardIndex hG r` is the standard index `r.data.J` of that
  family.
- `ParabolicRootPresentation.mono_groupHom_f`: the split component of a presentation maps
  monomorphically into its maximal split torus, since `f ≫ i = a ≫ l ≫ p` and the right side is
  a composite of monomorphisms.
- `ParabolicRootPresentation.range_radical_eq_standardUnipotent'`: a geometric unipotent radical
  `iU` of a presented parabolic has image `standardUnipotent i ν J`. The realization of the
  presentation by a standard cocharacter `ζ` identifies `P` and `M` with the dynamic parabolic
  and centralizer of `ζ`; `Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer`
  identifies the image of the radical with the dynamic unipotent subgroup, and
  `standardCocharacter` identifies the latter with the standard unipotent subgroup.

## Main theorem

`FamilyRegularComparison.exists_standardSource hG r hA hT hU hw hK hK' rho hsmooth hcalc`: let
`fam = r.standardFamily hG` and `I = r.standardIndex hG`, let `(w, c)` be a Weyl conjugation
from `P` to `Q`, and let `K` have Iwasawa coverage for `P` and `Q`. There are `c₂ : M' → M_I`
and Iwasawa coverage of `K` for `P_I` such that `(w, c₂)` is a Weyl conjugation from `P_I` to
`Q`, and the family comparison for `(P_I, Q, w, c₂)`, with the presentation
`⟨⟨T, i, ν, J, f I⟩, isCompatible I⟩` of `P_I` built from the data of `r`, implies the family
comparison for `(P, Q, w, c)`.

### Proof

The parabolic `P_I` and `P` have the same image (both are `standardParabolic i ν J` by the
compatibility fields `parabolic_eq`), and so do their Levis (`levi_eq`). Closed subgroups with
the same image are isomorphic over `G` (`IsClosedSubgroup.sourceIsoOfRangeEq`), which gives
`e : P_I ≅ P` over `G` and `eM : M ≅ M_I` compatible with the Levi inclusions. Put
`c₂ = c ≫ eM`. Then `(w, c₂)` is a Weyl conjugation, the radicals have the same image by
`range_radical_eq_standardUnipotent'` and `StandardParabolicFamily.range_radical_eq_standardUnipotent`,
and the transported parameters correspond along `e` by `parameterRestrict_comp`.
`FamilyRegularComparison.of_sourceRange` (module
`Langlands.Global.AdelicEisensteinFamilySourceRange`) concludes. Iwasawa coverage for `P_I`
follows from that for `P` by `IsIwasawaCompact.of_range_eq`.

## Source

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, take `P` standard. A root
presentation of `P` determines a standard family in which `P` has the same image as a standard
parabolic.
