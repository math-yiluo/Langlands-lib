# Almost-all level surjectivity from actual residue estimates

This derived internal module supplies the transition from a uniform numerical
residue-point estimate to almost-all surjectivity on the actual adelic level
factors of algebraic spaces. The estimate is an explicit premise; this
module does not prove Lang–Weil or construct a model to which it applies.

The curve-place theorem uses every global function field over a finite
constant field and every finite set `S` of actual curve places. The
number-field theorem uses every number field and every finite set `S` of
finite places. In each case the source and target are actual algebraic
spaces over the original ring of `S`-integers, and their smooth morphism
need not be representable.

The numerical premise counts the actual fibre of `RingPoints.map f` over
each point of the target with values in the native residue field of every
completed integer ring outside `S`. One nonnegative real constant and one
natural relative dimension control all these fibres. The conclusion is
surjectivity of the actual `RingPoints.map f` for cofinitely many indices
of `CurvePlaceLevelFactorIndex` or `NumberFieldLevelFactorIndex`. These
point types retain their original coefficient ring and its published
diagonal scalar actions.

The proof uses the published finiteness of places with bounded completed
residue cardinality. Its finite exceptional set contains all field factors
supported on `S`, all infinite places in the number-field case, and all
integral factors whose residue cardinality is at most the square of the
error constant. At each remaining integral factor, the published numerical
finite-field helper gives surjectivity on residue points. The native
completed integer ring is Henselian, its residue quotient is surjective,
and the published space lifting theorem gives surjectivity on integral
points. Thus no surjectivity assertion is needed at any of the finitely
many exceptional field factors.

The implementation composes published results on actual residues, cardinal
bounds and algebraic-space point maps. Separatedness, quasi-compactness,
geometric connectedness, finite type over the integers and a uniform
estimate must still be established when applying this result to an
arithmetic model. Varying relative dimensions and the final adelic
openness theorem remain separate obligations.

`cofiniteSpacePointLifts` packages any such established cofinite
surjectivity result as actual data: one finite exceptional index set and a
chosen lift, with its exact point-map equation, for every target point at
every other index. It uses the finite bad set given by the cofinite
statement and classical choice in each genuine point-map fibre. It works
over any original coefficient ring and dependent family of coefficient
algebras; the two arithmetic theorems above provide its cofinite premise
for the respective adelic level factors.
