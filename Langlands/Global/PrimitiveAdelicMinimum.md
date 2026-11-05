# Rational minima of primitive adelic heights

This module constructs a nonzero rational vector attaining the minimum of
the actual normalized primitive height after applying any fixed adelic
invertible matrix. The field is any number field `F : Type u`. For arbitrary
finite dimension `n`, including zero, it proves finiteness of bounded height
values and a strictly positive lower bound on all heights of nonzero rational
vectors. Constructing a nonzero minimizing vector requires `0 < n`.

The source motivation is T. A. Springer, *Reduction theory over global fields*
(1994), §1.10, printed p.210 (PDF p.4), the opening paragraph of the proof of
the GL(2) reduction proposition. That paragraph uses discreteness of rational
vectors and property (d) of §1.8 to obtain a positive lower bound and choose
a minimum. Registered original: `springer-1994-reduction-global-fields`,
SHA256 `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The implemented proof instead derives the stronger finiteness of bounded
height values from the compact representatives already constructed. This
is derived supporting content, specialized to number fields but retaining
arbitrary dimension. It does not invoke the GL(2) reduction proposition.

`rationalHeight F n g v` is `height F n (g.val *ᵥ rational F n v)`, where
`g` is an element of the actual adelic general linear group and `v` a rational
coordinate vector. The local norms are the maximum coordinate norms fixed
in `PrimitiveAdelicHeight`; the global product retains the multiplicity of
complex places. A nonzero rational vector gives an actual primitive adelic
vector after applying `g`, so its height is strictly positive. The rational
coordinate map is injective by injectivity of the diagonal field embedding.

The proof has three steps.

1. A compact subset of the actual adelic vector space meets the rational
   vector range in a finite set. Each compact coordinate image meets the
   closed discrete subgroup of principal adeles in a finite set, and a finite
   product of those finite sets is finite. Matrix multiplication on vectors
   is continuous, as each coordinate is a finite sum of continuous products.
   Applying the inverse of `g` therefore proves that only finitely many
   rational vectors can have their image under `g` in a prescribed compact
   set. These arguments use the existing principal-adele discreteness and
   closedness results with their actual adelic topology.

2. Fix a real bound `R`. The compact-representative theorem supplies a compact
   set `B` meeting the principal-scalar class of every primitive vector of
   height at most `R`. For a nonzero rational vector `v` with this bound, choose
   a nonzero rational scalar `a` such that `a g v` belongs to `B`. The scalar
   commutes with `g`, so `g (a v)` belongs to `B`; the first step gives only
   finitely many possible vectors `a v`. Principal scalar multiplication
   preserves height by the normalized product formula. Consequently the set
   of height values at most `R` is finite. This asserts finiteness of values,
   while allowing infinitely many rational scalar multiples of a vector.

3. Given any nonempty set `S` of nonzero rational vectors, choose `v₀` in `S`.
   The set of height values attained in `S` at most `height(g v₀)` is finite
   and nonempty. Its least value is attained by a vector `v` in `S`. Vectors
   above that bound also have height at least that of `v`, proving the
   unconditional minimum assertion on `S`. For `0 < n`, the constant vector
   with every coordinate one witnesses nonemptiness of the set of all
   nonzero rational vectors. The chosen minimizer `minimumRationalVector`
   is obtained by classical choice from this proved existence statement.
   Its nonvanishing and minimizing property are proved separately.
   `minimumRationalHeight` is its height and is strictly positive.

`exists_pos_le_rationalHeight` gives a positive lower bound for every dimension.
In positive dimension it uses the attained positive minimum. When `n = 0`,
there are no nonzero rational vectors, so the constant one is a valid bound.
The zero-dimensional case supplies no nonzero minimizer.

This construction supplies the rational minimum needed for a later reduction
argument. It does not prove local Iwasawa decomposition, the GL(2) Gauss
estimate, higher-rank induction, geometric setup or the full compatible
reductive Siegel-cover theorem.
