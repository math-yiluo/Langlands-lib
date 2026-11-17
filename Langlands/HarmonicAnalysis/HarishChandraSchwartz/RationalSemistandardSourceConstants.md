# Actual source constants for intrinsic semistandard spectral indices

Worker 268. This derived adapter supports Task 7258's weighted-synthesis
construction. It does not define an invariant family or a wave packet.

The source is Waldspurger (2003), *La formule de Plancherel pour les groupes
p-adiques*, registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
I.1, printed pages 240–241 (PDF pages 6–7), defines the common-compact source
normalization, proves independence of gamma from the parabolic with fixed
Levi, and defines `c(G|M)` from gamma and the rank-one gamma factors. VI.3,
printed page 305 (PDF page 71), and VII.2, printed page 319 (PDF page 85),
use the unquotiented synthesis and form coefficient constructed here.

The base field has arbitrary characteristic and universe `u`. It is an
arbitrary nonarchimedean local field with its canonical rational-point
topology. The connected reductive ambient group scheme is affine and
locally of finite type. No ambient splitness or quasi-splitness is imposed;
rank zero is included. No representation carrier or its topology enters
this scalar adapter.

`RationalSemistandard.CocharacterPresentation hG p` is auxiliary data: an
actual cocharacter of the fixed torus and equality of its entire dynamic
all-test triple with the intrinsic index `p`. It adds no coordinate to that
index. `CocharacterPresentation.ofCoverage` constructs such data only from
a witness of the published `SemistandardSpectralDynamicCoverageStatement`
and actual maximal splitness. That separately owned geometric target
remains an explicit obligation; it is not asserted as a theorem here.

The presentation's `hom` is the actual cocharacter morphism into `G`.
Its `parabolic_eq`, `levi_eq` and `radical_eq` are proved by projecting the
triple equality. `leviModel` uses the actual closed centralizer scheme,
its inclusion, its representability and its published reductivity.
`literalLeviHomeomorph` identifies the dynamic and intrinsic literal Levi
subgroups and fixes each ambient rational point. Thus the scalar package
is attached to the same actual subgroup, rather than an arbitrary positive
constant or an unrelated group model.

In namespace `RationalSemistandard.SourceConstants`, `gamma`, `c`,
`gammaReal` and `cReal` are exactly the published common-compact source
constants at that morphism/cocharacter and the displayed compact open
`K`. Its original source subgroup Haar normalizations are unchanged.
For a source application the common compact must have the source's
special-compact properties; the raw constants and their positivity are
defined for any supplied compact open. This file neither chooses such a
special compact nor asserts its existence.

`gamma_pos_ne_top` and `gammaReal_pos` specialize the published source
Haar positivity/finiteness theorems using actual smoothness from `hG`.
`c_pos_ne_top` and `cReal_pos` also use actual splitness of the maximal
split torus and the published finite rank-one-product theorem. No scalar
positivity or nonvanishing hypothesis is added.

`unquotientedWeight` is the real number

```text
(cReal^2)^(-1) * gammaReal^(-1)
  * |W^M| / (|W^G| * |P(M)|).
```

Here `W^G` is the actual relative Weyl quotient, `W^M` is
`semistandardLeviRelativeWeylSubgroup` for the literal all-test Levi, and
`P(M)` is the actual `SemistandardSpectralParabolicFiber`. Their natural
cardinalities are used directly. The definition requires no freely given
cardinal data. `unquotientedWeight_pos` consumes exactly the published
`SemistandardSpectralFiberFinitenessStatement`, which remains unproved
geometry owned by the full-index prerequisite. Ambient Weyl finiteness is
a published consequence of connected reductivity and maximal splitness,
Levi Weyl finiteness follows for its subgroup, and the parabolic fiber is
nonempty. Positivity then follows by positive inverse, product and quotient
rules. No Fourier-support conclusion is involved.

`RationalSemistandard.SourceConstantParabolicIndependenceStatement` is a
Prop-valued outstanding target for the actual displayed constants. Under
maximal splitness, a generic positive system and the published
`BruhatTits.SpecialCompact.SpecialCompactProperties` predicate for the
common compact, it concludes equality of the actual ENNReal gamma and c
for any two presentations whose intrinsic literal Levi functors agree.
This includes independence of the cocharacter presentation for a fixed
index. It assumes neither equality of constants nor positivity as data.
The source's fixed-Levi independence is not inferred merely from the
positive-multiple and compact-preserving conjugation comparisons already
proved in the Library. Its proof remains a substantive geometry/source-
normalization obligation. Equality of real values follows from its
ENNReal equalities when the target is supplied.

The source-special-compact and geometric coverage/finiteness obligations
remain visible. Existing scalar-conjugation, density and standard VI.3.1
owners are retained. This file proves no new density regularity, coefficient
normalization, integrability, Schwartz membership, synthesis factorization,
global form, VII.2.5 isometry or VIII finiteness/inversion.
