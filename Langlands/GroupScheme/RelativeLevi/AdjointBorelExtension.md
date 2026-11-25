# The sectioned adjoint Borel extension with its original radical

This internal construction combines the actual Borel and maximal-torus
stabilizer quotients with the sectioned Borel retraction. It retains the
original relative unipotent radical and constructs a split fppf quotient
from the adjoint Borel to the torus quotient. All group objects and maps
are actual group schemes and homomorphisms over the original base.

## Data and hypotheses

`RelativeLevi.AdjointBorelExtensionData i q a T t` is a Type-valued
structure over any scheme `S`. Its parameters are group schemes `B`, `G`
and `A`, homomorphisms `i : B → G` and `q : G → A`, an automorphic action
`a` of `A` on `G`, a commutative group scheme `T`, and `t : T → B`.
The structure retains:

- `borel`: the actual quotient-subgroup data for `i` and `q`, representing
  the stabilizer of the whole subgroup functor `range i` under `a`;
- `torus`: quotient-subgroup data for `t` and `borel.projection`,
  representing the stabilizer of `range (t ≫ i)` under the restricted
  action of `borel.group`;
- `retraction`: the sectioned smooth fppf Borel projection `p : B → T`,
  its original relative unipotent radical `U` with inclusion `r : U → B`,
  the multiplication isomorphism, and full kernel equality;
- `centerToTorus`, denoted `z : ker(q) → T`, whose composite with
  `t ≫ i` is the whole scheme-kernel inclusion of `q`;
- fppf quotient certificates identifying the full kernels of the actual
  Borel and torus projections with `range (z ≫ t)` and `range z`.

The two quotient-subgroup data fields include the actual groups, closed
inclusions, projections, cartesian squares and fppf properties. Their
stabilizer representation is on every relative test scheme, including
non-affine and nonreduced tests.

`IsRelativeBorelSubgroup.adjointBorelExtensionData` constructs these data
over `Spec R` for every commutative ring `R` and every universe. It assumes
that `G` is reductive, `i` is a relative Borel, `T` is a relative torus,
and `t ≫ i` is closed and fibrewise maximal. It also assumes an fppf
quotient `q` by the full subgroup functor `center G`, and that restricting
`a` along `q` is the conjugation action. The maximal torus and its
factorization through this Borel are supplied.

## Descended projection and unchanged radical

For data `d`, write `P = d.borel.group`, `D = d.torus.group`,
`qB = d.borel.projection`, `qT = d.torus.projection`,
`p = d.retraction.projection`, and `j = d.torus.inclusion`.
`d.projection` is the actual homomorphism `P → D` obtained by applying
`SectionedQuotientExtension.hom` to `p`, `t`, `z`, `qB` and `qT`.
`projection_fac` proves

`qB ≫ d.projection = p ≫ qT`.

`section_eq` proves `j ≫ d.projection = id D`. The proof cancels the
fppf epimorphism `qT`, uses the torus quotient square
`t ≫ qB = qT ≫ j`, substitutes `projection_fac`, and applies the
original section identity `t ≫ p = id T`.

`radical_mono` proves that the original composite `r ≫ qB : U → P`
is monic on underlying schemes over `S`. `isFppfQuotient` proves that
`d.projection` is flat, surjective and locally of finite presentation,
and that its full scheme-kernel range is exactly `range (r ≫ qB)`.
Both results apply the general sectioned quotient construction; the
monicity it needs for `r` follows from the relative radical's closedness.
The group `U` is the same group retained in the Borel retraction. It is
not replaced by a quotient of that radical.

`radical_isClosedSubgroup` adds closedness of `r ≫ qB` if the actual
target `D` is separated over `S`. This extra separation hypothesis is
explicit and is not needed for the data constructor, section,
monicity, or fppf quotient conclusion.

## Construction and provenance

The chosen Borel and torus quotients are constructed by
`adjointStabilizerData` and `adjointTorusStabilizerData`; the retraction is
constructed by `maximalTorusFppfRetractionData`. The proof then factors
`kernelι q` through the actual supplied maximal torus using
`relativeMaximalTorusCentralFactor`. Its centrality follows from the
assumed full-center kernel equality. The factor's composition theorem
gives `z ≫ (t ≫ i) = kernelι q`.

The Borel quotient's `kernel_eq` identifies its kernel with the inverse
image of the ambient kernel under `i`. Since `i` is monic, the factor
identity identifies this with `range (z ≫ t)` by
`SubgroupFunctor.comap_range_of_factor`. Applying the torus quotient's
`kernel_eq` and composition of inverse images gives the inverse image
under `t ≫ i`; the same factor lemma, using the ambient closed torus
inclusion's monicity, identifies this with `range z`. Thus the quotient
certificates needed by the general construction are proved from the
actual constructed quotient squares.

The private existence proof constructs `Nonempty` of the structure, and
the public definition selects a witness using `Classical.choice`.
This is derived internal content from the named Library constructions;
it is not a new source transcription.

This supporting module does not establish torus structure on `D`, an
induced-torus presentation, a vector-bundle series for `U`, cohomological
vanishing, or the exact semilocal inner-form theorem. Those remain
separate obligations.
