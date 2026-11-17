# Descent of compatible local section charts for one fixed module

This is an internal construction for the relative unipotent filtration project.
Let `S` and `X` be schemes in an arbitrary universe `u`, let `p : X ⟶ S`,
let `V` be a group scheme over `S`, and let `M` be an ordinary module sheaf on
`S`. `LocalSectionCharts p V M` records, for every test `T` over `S` and every
lift of `T` to `X`, a multiplicative equivalence between the actual group
`T ⟶ V.X` and the multiplicative presentation of the actual global sections
of `T.hom`-pullback of `M`. Its equations require naturality for the prescribed
relative `sectionPullback` and independence of the lift. These are supplied
chart data for one fixed downstairs sheaf, rather than a module-effectivity
assumption or a claim that arbitrary additive transition maps are linear.

Assume `p` is affine, flat and surjective and `M` is quasi-coherent.
`LocalSectionCharts.globalEquiv` constructs such an equivalence for every test,
without requiring that test to admit a lift. `globalEquiv_natural` proves its
naturality for exactly the section map in `RelativeUnipotent.Basic`. No affine
base, noetherian, finite-rank, nonempty-base or constant-rank hypothesis is used.
With the additional hypotheses that `V.X.hom` is affine and smooth and that `M`
is `IsFiniteLocallyFree`, `isVectorBundleAdditive` gives precisely
`IsVectorBundleAdditive V`.

The construction first pulls a test back along `p`. The chosen chart on this
cover gives a section for each point. Chart naturality and independence imply
the all-test matching equations `SectionCompatible`; the proved relative-section
descent theorem then gives `toSection`. A lifted test map factors through the
pullback cover. This factorization and independence identify its pulled-back
section with the supplied chart (`toSection_pullback_lift`). Faithful section
pullback proves global naturality. Injectivity follows from local chart
injectivity and epimorphicity of the scheme cover.

For surjectivity, apply the inverse local chart to the pullback of a given
section. Naturality and independence show that equal section pullbacks give
equal inverse-chart points (`inverse_equiv_matching`). Section pullback
composition therefore proves the represented-point matching equations on the
cover. `existsUnique_point_of_compatible` descends these points using the
published `EffectiveEpi` structure for quasi-compact flat surjections of schemes;
affineness supplies quasi-compactness. It checks the structure map to `S` and
uniqueness by cancellation of the epimorphism. Equality after faithful section
pullback then proves `toSection_surjective`. Finally `toSectionHom` verifies the
actual point group law after pullback to the cover, and `globalEquiv` combines
this homomorphism with the proved bijectivity.

The provenance is the published scheme effective-epimorphism theorem, the
actual relative-section descent interface, and elementary chart algebra. The
module includes their explicit specializations and does not invoke a new
structural theorem about reductive groups. Constructing these charts from an
actual linear module descent datum, reflecting finite local bases, and proving
the parent relative radical-filtration statement remain further obligations.
